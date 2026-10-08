from common_body_v1 import *

r=body_fixed()
targets=load(CONTRACT/'targets-v1.json')['targets']
names=[t['name'] for t in targets]
boundary=('This package adds exactly three derived AE causal proofs, not three printed results. '
    'It uses ambient-mu AE strong measurability and gives a classical law-relative globally bounded policy version on one all-time AE event; original off-null behavior need not be causal or unit-valued. '
    'It does not yet prove every completed/augmented-information or stochastic-kernel model has this representation, or design an executable unknown-law algorithm. '
    'General completed-information augmentation and universal causal stochastic-kernel realization remain REQUIRED, as do remaining Chapter1/2, unenumerated Chapters3–16 and necessary appendices. '
    'Original16 Chapter1 source objects and unknown(null) required proof total are preserved; no coverage percentage is inferred. The whole Goal remains ACTIVE. '
    'Local compiled candidates await combined/reader/FINAL/native/delivery gates. Stacked on OPEN draft unmerged PR197 exact4ca57025a2cdc4f4ba0d5cc2423b55786b0a7afe, base codex/research-online-c1-core-audit. Canonical main6847 and live site are unchanged; no merge or deployment.')
source=('Orabona arXiv:1912.13213v10,2026-06-21, SHA '+PDF_SHA+
    ': IID squared-loss variance benchmark and Eq(1.1)/(1.2), printed1/PDF13; strict-past prediction distinction, printed3/PDF15. '
    'These three statements are derived causal/AE formalization infrastructure, not three numbered or printed theorems. Source round1 corresponds to Lean time0.')
proof=('For each time, choose an F_t-measurable version of the original prediction under ambient mu. Lift measurability through F_t below the seed/strict-past comap and factor it as f_t(seed,history). '
    'Clip f_t with the existing unit-interval projection to obtain pi_t on every possible input. AE feasibility makes clipping fix the original value; countable intersection gives one event for every natural time. '
    'For independence, apply the genuine measurable private-seed/strict-past producer to the version, then transport independence back to the original prediction by AE equality. '
    'For the IID loss identity, measurability and AE bounds give L2, and derived current independence removes the cross term. The population mean attains the expected fixed unit-comparator benchmark; cancel T times the common variance and sum nonnegative squared deviations. '
    'The population mean is used only in analysis. Original predictions appear on both sides, and the same infinite process is used for every natural horizon, including T0.')
delta=('The source describes pathwise unit-valued guessing. L1 explicitly generalizes to AE feasibility/relative AE strong measurability and returns a globally unit-valued chosen version, with no off-null identity for the original. '
    'L1 allows arbitrary measure, arbitrary measurable Seed, and no ambient Y/S measurability, probability, IID or monotone F premise. '
    'L2 assumes probability, measurable joint-independent targets, measurable seed independent of the WHOLE infinite target stream, and subordinate F; it requires no support, same-law or L2 premise. '
    'L3 additionally needs identical target laws and AE unit bounds for targets/predictions. Current independence, attained comparator and regret identity are derived, not supplied. '
    'The benchmark is minimum of EXPECTED fixed unit losses outside expectation, not expected hindsight minimum. No rate, asymptotic success, convergence or high-probability claim follows.')
formula=r'\begin{aligned}F_t&\subseteq\sigma(S,Y_{<t}),\quad P_t\text{ has an }F_t\text{-measurable AE version},\\\exists(\pi_t)_{t\ge0}:\quad&\pi_t(s,h)\in[0,1]\ \text{for every }s,h,\\&P_t=\pi_t(S,Y_{<t})\quad\text{AE, simultaneously for all }t,\\P_t&\perp Y_t\quad\text{under joint independence and }S\perp(Y_t)_{t\ge0},\\R_T^{\mathrm{expected\ fixed}}&=\sum_{t<T}\mathbb E(P_t-\mathbb EY_0)^2\ge0.\end{aligned}'
card=dict(label='AE causal versions and original-process IID excess',pages='printed1,3 / PDF13,15',pdf_page=13,
    url='https://arxiv.org/pdf/1912.13213v10',math=formula,plain=proof,fallback=proof,relationship=source,
    contract=dict(model='One original real prediction process, arbitrary private measurable seed, strict finite past; explicit ambient-mu AE hypothesis.',
        assumptions=delta,parameters='One policy family before all horizons; one common AE event for all natural times. Time0 has empty history. L3 includes T0; no positive-horizon division.',
        regret='Minimum of expected squared losses over fixed unit comparators is outside expectation. Population mean is analysis-only, not a learner input.',
        guarantee=proof+' '+boundary),
    local_status=dict(status='compiled',label='Three new exact bodies and 14 AE-only canary proofs compiled locally; package gates pending',
        declarations=names,boundary=boundary))
items=[
    ('One bounded history policy agrees AE at every time',
     r'\exists\pi:\quad \forall t,\ \pi_t\text{ measurable},\quad\forall t,q,\ \pi_t(q)\in[0,1],\qquad\forall^{\mu\text{-AE}}\omega,\ \forall t,\ P_t(\omega)=\pi_t(S(\omega),Y_{<t}(\omega)).',
     'Choose each relative measurable version, factor through seed/strict past, and clip globally with projIcc. AE original feasibility makes clipping harmless; countable AE intersection gives one common event for all t.',
     'Arbitrary ambient measure and arbitrary measurable Seed; F_t below the seed/history comap, relative AE strong measurability and AE unit bounds. No ambient target/seed measurability, probability, IID or standard-Borel Seed premise. The real output has the standard-Borel structure used by factorization.',
     ['Measurable.exists_eq_measurable_comp','MeasureTheory.AEStronglyMeasurable.measurable_mk','MeasureTheory.ae_all_iff']),
    ('AE predictable original predictions are independent of the current target',
     r'Y_t\text{ jointly independent},\quad S\perp(Y_t)_{t\ge0},\quad F\subseteq\sigma(S,Y_{<t}),\quad P\text{ has an }F\text{-measurable AE version}\ \Longrightarrow\ P\perp Y_t.',
     'Apply the actual whole-stream seed/strict-past independence producer to the measurable version. IndepFun.congr transfers the conclusion to the original prediction, so current independence is produced rather than assumed.',
     'Probability, measurable jointly independent real targets, measurable seed independent of the WHOLE infinite stream, subordinate F, relative ambient-mu AE strong measurability. No bounds, identical laws, support or integrability premise; time0 is allowed.',
     ['BanditRL.OnlineLearning.predictable_private_seed_independent','ProbabilityTheory.IndepFun.congr']),
    ('Original AE causal IID excess equals mean-square error',
     r'\begin{aligned}R_T^{\mathrm{expected\ fixed}}&=\mathbb E\sum_{t<T}(P_t-Y_t)^2-\inf_{u\in[0,1]}\mathbb E\sum_{t<T}(u-Y_t)^2\\&=\sum_{t<T}\mathbb E(P_t-\mathbb EY_0)^2\ge0,\quad T\in\mathbb N.\end{aligned}',
     'Measurable seed/target histories lift relative AE measurability to the ambient field, and AE unit bounds yield L2. The new AE independence producer cancels the cross term. Substitute the attained expected fixed minimum T·Var(Y0), then sum nonnegative square integrals.',
     'Same original process for every natural T, jointly independent identically distributed measurable targets with AE unit support, private measurable seed independent of the entire stream, subordinate F_t and original AE measurable/unit predictions. Population mean is only an analysis witness. T0 is the empty-sum endpoint, with no convergence or rate.',
     [names[1],'BanditRL.OnlineLearning.expectedFixedMinimum_eq_variance','BanditRL.OnlineLearning.iid_cumulative_prediction_decomposition'])]
notes=[]
for i,(t,item) in enumerate(zip(targets,items)):
    title,math,idea,context,deps=item
    notes.append(dict(full_name=t['name'],title=title,chapter=ROUTE,featured=False,teaching_order=110+i,
        plain=idea,math=math,intuition='AE equality preserves the probabilistic result while the chosen history version is globally feasible.',
        why='Close the explicit AE causal bridge using the existing shared mathematical graph.',position=source,
        proof_idea=idea,lean_notes=context+' '+delta+' '+boundary,dependencies=deps))
proposal=dict(card=card,notes=notes,boundary=boundary,source=source,assumption_delta=delta,
    exact_R1_R6=load(CONTRACT/'reader-requirements-v1.json'),old_all_cards_notes_IDs_links_status_preserved=True,
    new_production_proofs=3,source_coverage_total=None,chapter_complete=False,goal_complete=False)
write(RUN/'reader-proposal-v1.json',proposal)

# Preserve exact prechange RAW pointers for the BODY receipt.
paths=[ROOT/'BanditRLProof.lean',ROOT/'Tests.lean']+READERS
snapshots=[]
for i,p in enumerate(paths):
    snapshot=RUN/'snapshots'/('BODY-mutable-integration-'+str(i)+'.raw')
    write(snapshot,p.read_bytes())
    snapshots.append(dict(path=p.as_posix(),sha256=sha(p),snapshot=snapshot.as_posix()))
write(RUN/'BODY-mutable-integration-bindings-v1.json',dict(rows=snapshots,
    BODY_receipt_sha256=BODY_SHA,current_live_will_change=True,not_claiming_original_live_RAW_unchanged=True))
for rel,addition in [('BanditRLProof.lean',b'\nimport BanditRLProof.OnlineGuessingAECausal\n'),
    ('Tests.lean',b'\nimport Tests.OnlineGuessingAECausalCanary\n')]:
    assert (ROOT/rel).read_bytes()==baseline(rel)
    (ROOT/rel).write_bytes(baseline(rel)+addition)
p=ROOT/'website/content/readings.json';d=load(p)
row=next(x for x in d['readings'] if x['slug']==ROUTE)
old_cards=len(row['source_theorems']);row['source_theorems'].append(card)
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
p=ROOT/'website/content/highlights.json';d=load(p)
assert not any(x['full_name'] in names for x in d['highlights'])
d['highlights']+=notes;p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
p=ROOT/'website/content/chapters.json';d=load(p)
row=next(x for x in d['chapters'] if x['slug']==ROUTE)
for k in ['completion_blockers','open_gaps']:row[k].append(boundary)
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf8'))

manifest=dict(schema_version='2.0',id=TASK,route='online-learning/chapter-1',frontier_cell=ROUTE,
    source_facing=True,source=dict(kind='book',title='Online Learning: A Modern Introduction Using Convex Optimization',
        version='arXiv:1912.13213v10,2026-06-21; SHA '+PDF_SHA,anchor='Three derived AE causal targets from IID squared-loss benchmark printed1/PDF13 and strict past printed3/PDF15',url='https://arxiv.org/pdf/1912.13213v10'),
    target='Three exact frozen AE causal producers, original-process fixed-expected excess, genuine AE-only positive-variance canary. '+boundary,
    affected_files=[PUBLIC.relative_to(ROOT).as_posix(),'BanditRLProof.lean']+[p.relative_to(ROOT).as_posix() for p in READERS],
    declarations=names,
    reuse_plan=dict(classification='adapt',decision='adapt_existing',
        searched_existing=['Actual pinned mathlib factorization/AE measurable mk/congruence/clipping APIs; actual native declaration/memory/paper/weapon retrieval. Full frozen whole-type VALUE proofs and compiled graph reviewed.'],
        reused_declarations=['Measurable.exists_eq_measurable_comp','ProbabilityTheory.IndepFun.congr','BanditRL.OnlineLearning.predictable_private_seed_independent','BanditRL.OnlineLearning.expectedFixedMinimum_eq_variance','BanditRL.OnlineLearning.iid_cumulative_prediction_decomposition'],
        new_shared_declarations=names,known_consumers=[names[2]],planned_consumers=['Required completed-information and general causal stochastic-kernel bridges'],
        no_duplicate_wrapper=True,decision_reason='Actual relative AE factorization and independence producers plus original-process performance endpoint; share existing real projection and probability parents rather than per-Book proofs.'),
    reader_contract=dict(source_anchor_visible=True,natural_language_formula_proof=True,hidden_assumptions_visible=True,
        source_vs_lean_delta_visible=True,lean_folded=True,dependencies_visible=True,remaining_boundary_visible=True),
    semantic_roundtrip=dict(required=True,status='accepted',formalizer='/root',blind_decoder='/root/osd_blind',source_reviewer='/root/source_reviewer',
        verdict=r['verdict'],remaining_semantic_delta='Derived source specialization/AE generalization explicitly reviewed at CONTRACT/BODY; exact R1-R6 future FINAL reader/combined/site gates pending. '+boundary),
    graph_contribution=dict(lean_graph='updated',overview_graph='updated',functor_hypergraph='none-found-with-reason',
        functor_reason='Routine AE representative/factorization/independence extension within one guessing model; no cross-setting transport or categorical result.',
        focus_targets=names,visual_review='Actual39 selected kernel graph nodes/2136 coalesced TYPE_VALUE edges/12 required VALUE pairs; shared registry/current site pixel review pending.',edge_semantics='formal-solid; overlays-dashed'),
    progress_updates=dict(teaching_route='updated: own source card and three exact proof notes, old cards/links/status preserved',
        banditrlwiki='no-change-with-reason: no Bandit case/setting/result changed',
        results_ledger='updated: three actual compiled candidates, zero accepted obligations until FINAL/native; original16/null and remaining full C1 required',
        roadmap='no-change-with-reason: whole16 Goal active and original SGB frontier preserved',website_surfaces=[p.relative_to(ROOT).as_posix() for p in READERS]),
    truth_boundary=boundary,
    verification=dict(focused_checks=['Actual Built module for all three frozen bodies and 14 canary proofs/one definition; complete public-type VALUE witnesses, 42 standard axiom records, 12 required VALUE pairs; exact fences'],
        bandit_check='Combinedroot/Tests/fullharness/stacked ANDmain contributor/ownshadow pending',
        site_build='Applicable isolated local site after combined gate pending; no deployment',
        site_check='Three exact public headers, shared old registry ID/URL/hash preservation, new nodes and original pixel checks pending',
        independent_review='Distinct staged CONTRACT118/BODY236 accepted-with-explicit-delta; exactR1-R6 future FINAL pending; reused automated roles, no absolute blind/human/external/runtime attestation',
        owned_test_files=[CANARY.relative_to(ROOT).as_posix()],owned_test_root_files=['Tests.lean']),
    contributor=dict(name='Codex for Ji Cheng',role='Formalizer, distinct staged automated decoder/source reviewer'))
write(MANIFEST,manifest)
write(RUN/'reader-integration-bindings-v1.json',dict(reader_proposal_sha256=sha(RUN/'reader-proposal-v1.json'),
    BODY_receipt_sha256=BODY_SHA,source_review_receipt_sha256=load(RUN/'stabilized-contract-v1.json')['receipt_sha256'],
    public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),old_source_cards_preserved=old_cards,
    new_source_cards=1,new_notes=3,original_R1_R6=r['required_reader_corrections'],
    all_old_readers_preserved=True,combined_and_FINAL_pending=True,chapter_complete=False,goal_complete=False))
from tools.check_contributor_contract import validate_contract
data,errors=validate_contract(MANIFEST.resolve())
write(RUN/'schema2-BODY-validation-v1.json',dict(errors=errors,semantic_status='CONTRACT/BODY only',FINAL_pending=True,chapter_complete=False,goal_complete=False))
assert not errors,errors
fixed_integrated()
print('Actual exact root/Test imports, one card/three notes and schema2 integrated; combined and FINAL pending.',flush=True)
