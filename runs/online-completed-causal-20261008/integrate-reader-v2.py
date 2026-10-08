from common_body_v2 import *

r=body_fixed()
targets=load(CONTRACT/'targets-v1.json')['targets'];names=[t['name'] for t in targets]
boundary=('Four derived completion proofs only, not four printed source results. '
    'The precise field is eventuallyMeasurableSpace F (ae ambient_mu): sets equal AE to F-measurable sets. '
    'No identity with completion of mu.trim F or arbitrary output-space version theorem is asserted. '
    'Classical real-valued measurable versions and one same-process all-time bounded history policy are law-relative; original off-null predictions need not be causal or unit. '
    'General causal stochastic-kernel realization remains REQUIRED, as do other source-required information constructions, remaining Chapter1/2, unenumerated Chapters3-16 and necessary appendices. '
    'Original16 Chapter1 source objects/null unknown proof total and all old reader statuses/links are preserved. Whole Goal ACTIVE. '
    'Four bodies and11nondegenerate canary proofs compiled locally; combined root/Tests/fullharness/current readers/site/FINAL/native/delivery still pending. '
    'Stacked on OPEN draft unmerged PR198 exact'+BASE+'. Canonical main6847 and live site unchanged; no merge/deployment.')
source=('Orabona arXiv:1912.13213v10,2026-06-21 SHA '+PDF_SHA+
    ': printed1/PDF13 IID squared-loss variance benchmark and Eqs1.1/1.2, printed3/PDF15 strict-past information. '
    'Completion terminology and these four declarations are derived formalization infrastructure/specializations, not four printed theorems. Printed round1 is Lean time0.')
core=('Embed real values measurably and injectively into countably many Bool coordinates. '
    'For each coordinate, augmented measurability supplies an F-measurable representative set with ambient-mu AE equality. '
    'Its membership bits form an F-measurable code. Countable intersection makes this code equal the original real code on one full-measure event. '
    'The measurable left inverse, extended to every code, produces an actual real F-measurable version equal to the original AE. '
    'The embedding is of the real output, so Omega requires no countability or standard-Borel assumption.')
policy=('Apply the actual real-version producer at each natural time, obtain relative AE strong measurability, and reuse the strict-past factorization/clipping producer. '
    'Original predictions are AE in[0,1] at every time; clipping gives global feasibility on every seed/history input. One countable intersection gives one AE event for all natural times and one family before all horizons.')
independence=('Obtain a relative measurable version from the completed-field hypothesis. '
    'Use the actual private-seed/strict-past independence producer and AE congruence. Joint target independence and seed independence of the WHOLE infinite stream derive independence of the ORIGINAL prediction and current target. '
    'No support, same-law, boundedness or prediction-integrability assumption is needed in this independence terminal.')
excess=('Actual completed-information versions supply the accepted AE producer, which derives current independence and bounded L2. '
    'The population mean attains minimum EXPECTED fixed unit-comparator loss outside expectation. The common target variance cancels in cumulative expected loss, leaving the sum of original squared deviations. '
    'Original predictions appear on both sides, the same infinite process is used for all natural horizons, and T0 is an empty identity. The population mean is analysis-only; no convergence, rate, pathwise or high-probability statement follows.')
delta=('Core: arbitrary ambient measure and separate F; real augmented-field measurability only, no probability/finiteness/F<=ambient/Omega regularity. '
    'Bounded history policy: F_t below seed plus strict past, original completed-measurable P_t and original AE[0,1] for EVERY natural time; no probability or ambient seed/target measurability is needed. '
    'Independence: probability, measurable joint-independent targets, measurable seed independent of the whole stream and subordinate F; no boundedness/same-law/support premise. '
    'IID identity additionally assumes same target laws and AE unit targets/predictions. No supplied version/current independence/regret bound. '
    'Source pathwise feasibility is explicitly generalized to AE original feasibility; chosen policy remains globally feasible. '
    'Ambient null augmentation is exact; completion of mu.trim F is a different construction without an asserted equivalence. Real codomain regularity is used. '+boundary)
card=dict(label='Ambient completed information gives real causal versions',pages='printed1,3 / PDF13,15',pdf_page=13,
    url='https://arxiv.org/pdf/1912.13213v10',
    math=r'\begin{aligned}\overline{F}^{\mu}&=\{A:\exists B\in F,\ A=_{\mu\text{-AE}}B\},\\P\text{ measurable on }\overline{F}^{\mu}&\Longrightarrow\exists Q\text{ measurable on }F,\ P=Q\quad\mu\text{-AE},\\F_t\subseteq\sigma(S,Y_{<t}),\ P_t\in[0,1]\text{ AE}&\Longrightarrow P_t=\pi_t(S,Y_{<t})\quad\text{AE for all }t,\\R_T^{\mathrm{expected\ fixed}}&=\sum_{t<T}\mathbb E(P_t-\mathbb EY_0)^2\ge0.\end{aligned}',
    plain=core+' '+policy+' '+independence+' '+excess,fallback=core+' '+policy+' '+independence+' '+excess,
    relationship=source,contract=dict(model='One original real prediction process; ambient-mu null-augmented strict-past sigma fields, arbitrary measurable private seed.',
        assumptions=delta,parameters='One policy family/all-time AE event before all horizons; time0 empty strict past. Every natural T/T0, no horizon division.',
        regret='Minimum of expected fixed unit losses outside expectation; population mean analysis-only.',
        guarantee=core+' '+policy+' '+independence+' '+excess+' '+boundary),
    local_status=dict(status='compiled',label='Four exact public bodies and11genuine completed-but-not-ordinary canary proofs compiled locally; package gates pending',boundary=boundary))
proofs=[core,policy,independence,excess]
maths=[r'\begin{aligned}\phi:\mathbb R\hookrightarrow\{0,1\}^{\mathbb N},\quad A_n\in F,\\1_{A_n}=\phi(P)_n\ \text{AE for all }n\quad&\Longrightarrow\quad Q=\phi^{-1}((1_{A_n})_n),\\Q\text{ is }F\text{-measurable},\quad&P=Q\ \mu\text{-AE}.\end{aligned}',
    r'\begin{aligned}F_t\subseteq\sigma(S,Y_{<t}),\quad P_t\in[0,1]\text{ AE},\\P_t\text{ is }\overline F_t^\mu\text{-measurable}\quad&\Longrightarrow\quad\exists(\pi_t),\\\pi_t(s,h)\in[0,1]\text{ for every input},\quad&P_t=\pi_t(S,Y_{<t})\text{ AE simultaneously for all }t.\end{aligned}',
    r'\begin{aligned}P_t\text{ is }\overline F_t^\mu\text{-measurable},\quad F_t\subseteq\sigma(S,Y_{<t}),\\(Y_t)_t\text{ jointly independent},\quad S\perp(Y_t)_{t\ge0}\quad&\Longrightarrow\quad P_t\perp Y_t.\end{aligned}',
    r'\begin{aligned}R_T^{\mathrm{expected\ fixed}}&:=\mathbb E\sum_{t<T}(P_t-Y_t)^2-\inf_{u\in[0,1]}\mathbb E\sum_{t<T}(u-Y_t)^2,\\R_T^{\mathrm{expected\ fixed}}&=\sum_{t<T}\mathbb E(P_t-\mathbb EY_0)^2\ge0,\quad T\in\mathbb N.\end{aligned}']
titles=['A real version from ambient null-augmented measurability','One bounded history policy from completed information',
    'Original current independence from completed information','Original expected-fixed excess for completed predictors']
prior=['BanditRL.OnlineLearning.ae_predictable_exists_bounded_history_policy',
    'BanditRL.OnlineLearning.ae_predictable_private_seed_independent',
    'BanditRL.OnlineLearning.ae_predictable_private_seed_expectedFixed_excess']
notes=[]
for i,t in enumerate(targets):
    deps=[] if i==0 else [names[0],prior[i-1]]
    external=('Actual pinned Mathlib VALUE parents: MeasurableSpace.measurable_mapNatBool, MeasurableSpace.injective_mapNatBool, '
        'Measurable.measurableEmbedding, MeasurableEmbedding.measurable_invFun, MeasurableEmbedding.leftInverse_invFun, MeasureTheory.ae_all_iff. '
        'No ABRL parent link is fabricated for this core.') if i==0 else 'Measurable.aestronglyMeasurable and AEStronglyMeasurable.congr transfer the actual core version under the ambient measure.'
    notes.append(dict(full_name=t['name'],title=titles[i],chapter=ROUTE,featured=False,teaching_order=120+i,
        plain=proofs[i],math=maths[i],intuition='Ambient null changes can alter off-null behavior while preserving the original probabilistic endpoint.',
        why='Close the precise ambient completed-information edge and connect it to the existing original-process terminal.',
        position=source,proof_idea=proofs[i],lean_notes=delta+' '+external,dependencies=deps))
proposal=dict(card=card,notes=notes,boundary=boundary)
write(RUN/'reader-proposal-v1.json',proposal)
for rel,addition in r['approved_future_exact_scope']['exact_root_additions'].items():
    p=ROOT/rel;assert p.read_bytes()==baseline(rel);p.write_bytes(p.read_bytes()+addition.encode())
for label in ['readings','highlights','chapters']:
    p=ROOT/'website/content'/(label+'.json');data=load(p)
    if label=='highlights':
        assert not any(x['full_name'] in names for x in data[label]);data[label]+=notes
    else:
        row=next(x for x in data[label] if x['slug']==ROUTE)
        if label=='readings':row['source_theorems'].append(card)
        else:
            for k in ['completion_blockers','open_gaps']:row[k].append(boundary)
            row['module_globs'].append(PUBLIC.relative_to(ROOT).as_posix())
    p.write_bytes((json.dumps(data,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
manifest=dict(schema_version='2.0',id=TASK,route='online-learning/chapter-1',frontier_cell=ROUTE,source_facing=True,
    source=dict(kind='book',title='Online Learning: A Modern Introduction Using Convex Optimization',
        version='arXiv:1912.13213v10,2026-06-21; SHA '+PDF_SHA,anchor='Four derived ambient-completion targets, printed1/PDF13 and printed3/PDF15',url='https://arxiv.org/pdf/1912.13213v10'),
    target='Actual real-version producer from ambient augmented measurability, original causal endpoints. '+boundary,
    affected_files=[PUBLIC.relative_to(ROOT).as_posix(),'BanditRLProof.lean']+[p.relative_to(ROOT).as_posix() for p in READERS],declarations=names,
    reuse_plan=dict(classification='adapt',decision='adapt_existing',searched_existing=['Actual pinned countable coding/measurable inverse/EventuallyMeasurable APIs and prior actual AE producers; native shared retrieval index records.'],
        reused_declarations=prior+['MeasurableSpace.measurable_mapNatBool','Measurable.measurableEmbedding','MeasurableEmbedding.measurable_invFun'],
        new_shared_declarations=names,known_consumers=names[1:],planned_consumers=['Required general causal stochastic-kernel realization'],
        no_duplicate_wrapper=True,decision_reason='One actual canonical real-version producer serves three genuine completed-field consumers; prior causal proofs are reused without duplication.'),
    reader_contract=dict(source_anchor_visible=True,natural_language_formula_proof=True,hidden_assumptions_visible=True,
        source_vs_lean_delta_visible=True,lean_folded=True,dependencies_visible=True,remaining_boundary_visible=True),
    semantic_roundtrip=dict(required=True,status='accepted',formalizer='/root',blind_decoder='/root/osd_blind',source_reviewer='/root/source_reviewer',
        verdict=r['verdict'],remaining_semantic_delta='Distinct CONTRACT175/BODY285 accept derived real/completed-field delta; exact R1-R7 FINAL pending. '+boundary),
    graph_contribution=dict(lean_graph='integration-node',overview_graph='updated',functor_hypergraph='none-found-with-reason',
        functor_reason='Local measurable-version/causal-information integration in one guessing model; no cross-setting or categorical claim.',
        focus_targets=names,visual_review='Actual52selected nodes2614coalesced TYPE_VALUE edges18required VALUE pairs; current shared Book/root/site/pixels pending.',edge_semantics='formal-solid; overlays-dashed'),
    progress_updates=dict(teaching_route='updated: own source card/four notes/precise module ownership, old entries/links/statuses intact',
        banditrlwiki='no-change-with-reason: no Bandit setting changed',results_ledger='updated: four actual compiled candidates, zero accepted until full gates; original16/null preserved',
        roadmap='no-change-with-reason: whole16 Goal and global SGB preserved',website_surfaces=[p.relative_to(ROOT).as_posix() for p in READERS]),
    truth_boundary=boundary,verification=dict(focused_checks=['Four actual Built bodies;11named canary proofs;4whole proof VALUE checks/56standard-only axioms/18VALUEpairs/4fences'],
        bandit_check='Combinedroot/Tests/fullharness/bothcontributorbases/ownshadow pending',site_build='Applicable isolated local site after combined gate pending',
        site_check='10938old registry preservation/four exact headers/actual original pixel review pending',
        independent_review='Distinct staged CONTRACT175/BODY285 accepted-with-explicit-delta, R1-R7 FINAL pending; reused automated history, no absolute blind/human/external/runtime attestation',
        owned_test_files=[CANARY.relative_to(ROOT).as_posix()],owned_test_root_files=['Tests.lean']),
    contributor=dict(name='Codex for Ji Cheng',role='Formalizer, distinct staged automated decoder/source reviewer'))
write(MANIFEST,manifest)
from tools.check_contributor_contract import validate_contract
data,errors=validate_contract(MANIFEST.resolve())
write(RUN/'schema2-validation-v1.json',dict(errors=errors,CONTRACT_BODY_only=True,FINAL_pending=True,goal_complete=False))
assert not errors,errors
write(RUN/'reader-integration-bindings-v1.json',dict(proposal_sha256=sha(RUN/'reader-proposal-v1.json'),
    BODY_receipt_sha256=BODY_SHA,public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),new_source_cards=1,new_notes=4,
    exact_one_module_globs_addition=True,external_mathlib_links_not_fabricated=True,old_readers_preserved=True,full_gates_pending=True))
fixed_integrated()
print('Actual exact root/Test, one source card/four notes, precise shared Book module mapping and valid schema2 integrated; combined/FINAL gates pending.',flush=True)
