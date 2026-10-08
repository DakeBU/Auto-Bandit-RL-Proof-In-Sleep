from common_integrated_v1 import *
r=body_fixed()
proposal=load(RUN/'reader-proposal-v1.json')
for p in READER_FILES:
    assert p.read_bytes()==original(p).read_bytes(),p
write(RUN/'BODY-integration-authorization-v1.json',dict(receipt_sha256=BODY_SHA,
    report_sha256=BODY_REPORT_SHA,actual_fixed_rows=r['fixed_input_count'],
    future_scope=r['future_integration_scope_verdict'],exact_R1_R8=r['reader_requirements']))
for p,addition in [('BanditRLProof.lean',b'\nimport BanditRLProof.OnlineGuessingIIDSuccess\n'),
    ('Tests.lean',b'\nimport Tests.OnlineGuessingIIDSuccessCanary\n')]:
    Path(p).write_bytes(original(p).read_bytes()+addition)
p=Path('website/content/readings.json');d=load(p)
row=next(x for x in d['readings'] if x['slug']==ROUTE)
assert len(row['source_theorems'])==13
row['source_theorems'].append(proposal['card'])
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
p=Path('website/content/highlights.json');d=load(p)
old={x['full_name'] for x in d['highlights']}
assert all(n['full_name'] not in old for n in proposal['notes'])
d['highlights'].extend(proposal['notes'])
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
p=Path('website/content/chapters.json');d=load(p)
row=next(x for x in d['chapters'] if x['slug']==ROUTE)
row['module_globs'].append(PUBLIC.as_posix())
for k in ['completion_blockers','open_gaps']: row[k].append(proposal['boundary'])
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
names=[r['name'] for r in load(CONTRACT/'targets-v1.json')['targets']]
reuse=[PRE+x for x in ['normalized_excess','expectedFixedRegret','expectedFixedMinimum',
    'expectedFixedMinimum_eq_variance','expected_fixed_prefix_decomposition',
    'randomized_history_policy_expectedFixed_excess','meanPredict_expectedFixed_excess',
    'theorem_1_3','empiricalMean_minimizes','meanPredict_measurable','meanPredict_mem']]
reuse+=['Asymptotics.isLittleO_iff_tendsto\'','MeasureTheory.integral_mono_ae',
    'MeasureTheory.integral_sub','MeasureTheory.integrable_finset_sum','Real.tendsto_pow_log_div_mul_add_atTop']
manifest=dict(schema_version='2.0',id=TASK,route='online-learning/chapter-1',frontier_cell=ROUTE,
    source_facing=True,source=dict(kind='book',title='Online Learning: A Modern Introduction Using Convex Optimization',
        version='arXiv:1912.13213v10,2026-06-21; SHA '+PDF_SHA,
        anchor='printed1–2/PDF13–14 Eq1.1/1.2 success; derived stochastic application of Theorem1.3 printed4/PDF16',
        url='https://arxiv.org/pdf/1912.13213v10'),
    target='Four adapters/derived applications: centered-total success equivalence, actualprivate-seed policy criterion, actualmeanPredict no-independence expected-fixed4logupper andactualIIDordinaryzero/little-o. '+proposal['boundary'],
    affected_files=[PUBLIC.as_posix(),'BanditRLProof.lean','website/content/readings.json',
        'website/content/highlights.json','website/content/chapters.json'],declarations=names,
    reuse_plan=dict(classification='adapt',decision='adapt_existing',
        searched_existing=['Actual native retrieval and selected typedAPI/kernel queries, plus compiled actualTYPE/VALUE graph; retained APIquery failures'],
        reused_declarations=reuse,new_shared_declarations=names,
        known_consumers=[PRE+'randomized_history_policy_success_iff',PRE+'meanPredict_iid_success'],
        planned_consumers=[],no_duplicate_wrapper=True,
        decision_reason='Normalize existing causalexpectedfixed producers and integrate actualsource meanPredictupper; do not duplicate asymptotic/probability foundations.'),
    reader_contract=dict(source_anchor_visible=True,natural_language_formula_proof=True,
        hidden_assumptions_visible=True,source_vs_lean_delta_visible=True,lean_folded=True,
        dependencies_visible=True,remaining_boundary_visible=True),
    semantic_roundtrip=dict(required=True,status='accepted',formalizer='/root',blind_decoder='/root/osd_blind',
        source_reviewer='/root/source_reviewer',verdict=r['verdict'],
        remaining_semantic_delta='Bounded CONTRACT/BODY mathematical semantics accepted; exactR1–R8/current reader/FINAL andnativepackage acceptance pending. '+proposal['boundary']),
    graph_contribution=dict(lean_graph='integration-node',overview_graph='updated',
        functor_hypergraph='none-found-with-reason',functor_reason='One scalar IID benchmark normalization and derived convergence; no cross-setting transport proof.',
        focus_targets=names,visual_review='Actual45selectedkernel/graph nodes and14directVALUEpairs; sharedregistry/site/currentpixels pending.',
        edge_semantics='formal-solid; overlays-dashed'),
    progress_updates=dict(teaching_route='updated: one sourcequalifiedsuccesscard/fournotes/ownmodule mapping; oldcards/notes/IDs retained',
        banditrlwiki='no-change-with-reason: no Bandit setting/result changed',
        results_ledger='updated: own bounded four terminal closure, original16objects/proof-totalnull/wholeC1open',
        roadmap='no-change-with-reason: sequential16chapter Goal active; globalSGBunchanged',
        website_surfaces=['website/content/readings.json','website/content/highlights.json','website/content/chapters.json']),
    truth_boundary=proposal['boundary'],verification=dict(
        focused_checks=['Four exactpublicVALUEs, fourwholeProp/threedefidentities,14 actualcanaryproofs/2definitions,45namedkernelchecks standardaxioms,45nodecompilergraph3325TYPE/VALUEoccurrences and14requiredactualVALUEpairs; allheadersunchanged'],
        bandit_check='Combinedroot/Tests/fullharness/ownshadow/PR-basecontributor pending; main-relativefiveoldauditCI failure notwaived',
        site_build='Applicablelocalbuild aftercombinedLean gate pending',site_check='Registry/currentDOM/pixels pending',
        independent_review='Distinct CONTRACT88/BODY128inputs accepted-with-explicit-delta; exactR1-R8/FINAL remainpending; automatedreusedactors,nohuman/external/absoluteblind/runtimeattestation',
        owned_test_files=[CANARY.as_posix()],owned_test_root_files=['Tests.lean']),
    contributor=dict(name='Codex for Ji Cheng',role='Formalizer/sharedintegration; distinct stagedautomateddecoder/source reviewer'))
write(MANIFEST,manifest)
write(RUN/'owned-suffix-bindings-v1.json',dict(suffixes={p.as_posix():dict(
    sha256=hashlib.sha256(b'').hexdigest(),text='') for p in APPEND_METADATA},
    zero_new_metadata_suffix_at_integration=True))
fixed_integrated()
from tools.check_contributor_contract import validate_contract
data,errors=validate_contract(MANIFEST.resolve())
write(RUN/'schema2-BODY-validation-v1.json',dict(errors=errors,semantic_status='accepted boundedCONTRACT/BODYonly',
    FINAL_pending=True,chapter_complete=False,goal_complete=False))
assert not errors,errors
write(RUN/'reader-integrated-bindings-v1.json',dict(public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    old_source_cards=13,new_source_cards=1,new_proof_notes=4,new_shared_publicnodes=4,
    oldcards_notes_preserved=True,BODY_receipt_sha256=BODY_SHA,
    original_R1_R8=r['reader_requirements'],combined_gates_pending=True,
    chapter_complete=False,goal_complete=False))
print('Exact scopedroot/Testimports andone sourcecard/fournotes integrated after BODY; schema2 validates, combined/FINAL gates pending.')
