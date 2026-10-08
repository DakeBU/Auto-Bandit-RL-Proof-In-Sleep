from common_body_v2 import *
r=body_fixed();scope=r['approved_future_exact_scope']
for rel,addition in scope['exact_root_additions'].items():
    p=ROOT/rel;assert addition.strip().encode('utf8') not in p.read_bytes()
    p.write_bytes(p.read_bytes()+addition.encode('utf8'))
proposal=load(RUN/'reader-proposal-v1.json');names=[t['name'] for t in load(CONTRACT/'targets-v1.json')['targets']]
for p in READERS:
    label=p.stem;d=load(p)
    if label=='highlights':
        assert not any(x['full_name'] in names for x in d[label]);d[label]+=proposal['notes']
    else:
        row=next(x for x in d[label] if x['slug']=='online-foundations')
        if label=='readings':row['source_theorems'].append(proposal['card'])
        else:
            for key in ['completion_blockers','open_gaps']:row[key].append(proposal['boundary'])
            row['module_globs'].append(PUBLIC.relative_to(ROOT).as_posix())
    p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
boundary=proposal['boundary'];newnames=['BanditRL.OnlineLearning.dyadicObservation']+names
manifest=load(ROOT/'research-wiki/contribution-contracts/online-ftl-limit-20261009.json')
manifest.update(id=TASK,source=dict(kind='book',title='Online Learning: A Modern Introduction Using Convex Optimization',
    version='arXiv:1912.13213v10,2026-06-21; SHA '+PDF_SHA,
    anchor='Four derived bounded actual-FTL reconciliation endpoints, printed2/PDF14, Theorem1.3 printed4/PDF16, printed6/PDF18',
    url='https://arxiv.org/pdf/1912.13213v10'),target=boundary,
    affected_files=[PUBLIC.relative_to(ROOT).as_posix(),'BanditRLProof.lean']+[p.relative_to(ROOT).as_posix() for p in READERS],
    declarations=newnames,truth_boundary=boundary)
manifest['reuse_plan']=dict(classification='adapt',decision='adapt_existing',
    searched_existing=['Actual shared fixed-limit criterion, conditional literal producer, empirical-mean feasibility, actual upper-FTL and best-average limit; pinned Mathlib powers/inverse-limit APIs. Exact four new names searched and absent.'],
    reused_declarations=['BanditRL.OnlineLearning.meanPredict_fixedRegret_limit_iff','BanditRL.OnlineLearning.meanPredict_limitNoRegret_of_mean_converges',
        'BanditRL.OnlineLearning.empiricalMean_mem','BanditRL.OnlineLearning.meanPredict_noRegret',
        'BanditRL.OnlineLearning.meanPredict_bestRegret_average_tendsto_zero'],
    new_shared_declarations=newnames,known_consumers=[names[3]],planned_consumers=['Required full Chapter1 source reconciliation and chapter gate'],
    no_duplicate_wrapper=True,decision_reason='Derive the actual bounded oscillation and exact all-comparator iff using one fixed stream/learner; no support, mean convergence or regret oracle.')
manifest['semantic_roundtrip']=dict(required=True,status='accepted',formalizer='/root',blind_decoder='/root/osd_blind',source_reviewer='/root/source_reviewer',
    verdict=r['verdict'],remaining_semantic_delta='Separate CONTRACT189/CANARY42/BODY390 favorable; four DERIVED results and exact future integration reviewed. Full FINAL pending. '+boundary)
manifest['graph_contribution']=dict(lean_graph='new-node',overview_graph='updated',functor_hypergraph='none-found-with-reason',
    functor_reason='Same-source same-process comparator limit reconciliation; no cross-setting/categorical transport theorem.',focus_targets=names,
    visual_review='Four whole proof VALUE witnesses,28 standard-only axiom outputs,24 selected nodes/19 directVALUEpairs; applicable new site/pixels pending.',
    edge_semantics='formal-solid; overlays-dashed')
manifest['progress_updates']=dict(teaching_route='updated: one sourcecard/four notes/one production module; all older records/status/URLs retained',
    banditrlwiki='no-change-with-reason: no Bandit setting change',results_ledger='updated: four focused compiled candidates,0 accepted until full gates; original16/null preserved',
    roadmap='no-change-with-reason: whole16 Goal/globalSGB frontier unchanged',website_surfaces=[p.relative_to(ROOT).as_posix() for p in READERS])
manifest['verification']=dict(focused_checks=['Four actual body proofs/11 public canary proofs/4 whole VALUE witnesses/28 standard-only axiom outputs/19 direct VALUE pairs/15 fences'],
    bandit_check='New combinedroot/Tests/fullharness/both nonempty committed-HEAD contributorbases/ownshadow pending',
    site_build='Applicable clean current local site after new combined Lean gate pending',
    site_check='10964 complete oldregistry records plus4 production theorems/1 definition and current originalpixels pending',
    independent_review='Distinct staged CONTRACT189/CANARY42/BODY390 favorable; FINAL pending. Reused automated actors, no human/external/absolute-blind/runtimeattestation.',
    owned_test_files=[CANARY.relative_to(ROOT).as_posix()],owned_test_root_files=['Tests.lean'])
write(CONTRIBUTION,manifest)
from tools.check_contributor_contract import validate_contract
_,errors=validate_contract(CONTRIBUTION.resolve());write(RUN/'schema2-validation-v1.json',dict(errors=errors,package_acceptance_pending=True,goal_complete=False));assert not errors,errors
integrated_fixed()
write(RUN/'reader-integration-bindings-v1.json',dict(public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    body_receipt_sha256=sha(RUN/'public-body-receipt-v1.json'),proposal_sha256=sha(RUN/'reader-proposal-v1.json'),
    new_guard_sha256=sha(RUN/'common_body_v2.py'),original_guard_artifacts_immutable=True,old_reader_records_preserved=True,
    source_card_count_before=19,source_card_count_after=20,new_notes=4,new_module_entries=1,
    combined_full_gates_pending=True,chapter_complete=False,goal_complete=False))
print('Exact separate BODY-reviewed root/Test/reader delta applied; full acceptance pending.',flush=True)
