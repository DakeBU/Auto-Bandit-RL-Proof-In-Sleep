from common_body_v1 import *
import gzip
r=body_fixed()
scope=r['approved_future_exact_scope']
paths=list(scope['exact_root_additions'])+scope['reader_files']+[
    'research-wiki/retrieval-index/'+n+'.json' for n in ['bandit_paper_cards','bandit_scenario_cards',
    'bandit_textbook_cards','proof_weapon_cards','local_leaf_cards','local_lean_declarations']]
baseline=[]
for rel in paths:
    p=ROOT/rel
    raw=p.read_bytes()
    committed=subprocess.check_output(['git','show',BASE+':'+rel])
    assert raw.replace(b'\r\n',b'\n')==committed.replace(b'\r\n',b'\n'),rel
    snap=RUN/'integration-baseline'/(rel.replace('/','--')+'.raw')
    write(snap,raw)
    baseline.append(dict(path=rel,sha256=sha(p),snapshot=snap.as_posix()))
write(RUN/'integration-baseline-v1.json',dict(rows=baseline,old_production_registry_nodes=10959))
oldregistry=ROOT/'tmp/online-kernel-causal-site-v1/books/registry.json'
old=load(oldregistry)
assert len(old['nodes'])==10959 and old['lean_verified']
write(RUN/'registry-baseline-v1.json.gz',gzip.compress(oldregistry.read_bytes(),mtime=0))
write(RUN/'registry-baseline-bindings-v1.json',dict(path=oldregistry.as_posix(),raw_sha256=sha(oldregistry),
    gzip_sha256=sha(RUN/'registry-baseline-v1.json.gz'),old_complete_node_records=10959,
    identity=old['identity'],source_commit=old['source_commit'],cached_old_site_not_fresh_current_build=True))
for rel,addition in scope['exact_root_additions'].items():
    p=ROOT/rel
    assert not addition.strip().encode('utf8') in p.read_bytes()
    p.write_bytes(p.read_bytes()+addition.encode('utf8'))
proposal=load(RUN/'reader-proposal-v1.json')
names=[t['name'] for t in load(CONTRACT/'targets-v1.json')['targets']]
for p in READERS:
    label=p.stem
    d=load(p)
    if label=='highlights':
        assert not any(x['full_name'] in names for x in d[label])
        d[label]+=proposal['notes']
    else:
        row=next(x for x in d[label] if x['slug']=='online-foundations')
        if label=='readings':
            row['source_theorems'].append(proposal['card'])
        else:
            for key in ['completion_blockers','open_gaps']:
                row[key].append(proposal['boundary'])
            row['module_globs'].append(PUBLIC.relative_to(ROOT).as_posix())
    p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
boundary=proposal['boundary']
manifest=dict(schema_version='2.0',id=TASK,route='online-learning/chapter-1',frontier_cell='online-foundations',source_facing=True,
    source=dict(kind='book',title='Online Learning: A Modern Introduction Using Convex Optimization',
        version='arXiv:1912.13213v10,2026-06-21; SHA '+PDF_SHA,
        anchor='Derived actual FTL limit hinges; printed2/PDF14, Theorem1.3 printed4/PDF16 and printed6/PDF18',
        url='https://arxiv.org/pdf/1912.13213v10'),
    target='Same actual FTL lower gap, signed comparator identity, best/T zero and exact ordinary fixed-limit criterion with conditional literal producer. '+boundary,
    affected_files=[PUBLIC.relative_to(ROOT).as_posix(),'BanditRLProof.lean']+[p.relative_to(ROOT).as_posix() for p in READERS],
    declarations=names,
    reuse_plan=dict(classification='adapt',decision='adapt_existing',
        searched_existing=['Actual native meanPredict/minimum/LimitNoRegret statements, pinned Mathlib limitAPI/cross-checked theorem cards; no external dependency.'],
        reused_declarations=['BanditRL.OnlineLearning.empiricalMean_minimizes','BanditRL.OnlineLearning.empiricalMean_decomposition',
            'BanditRL.OnlineLearning.squaredBestRegret_eq_comparatorRegret','BanditRL.OnlineLearning.meanPredict_bestRegret_bound'],
        new_shared_declarations=names,known_consumers=names[2:],
        planned_consumers=['Required concrete bounded oscillating-mean source obstruction and all-comparator ordinary-limit converse'],
        no_duplicate_wrapper=True,decision_reason='Reuse actual prefixminimum/4log producer and add same-FTL lower and exactlimit compatibility; no regret or convergence oracle replaces the terminal.'),
    reader_contract=dict(source_anchor_visible=True,natural_language_formula_proof=True,hidden_assumptions_visible=True,
        source_vs_lean_delta_visible=True,lean_folded=True,dependencies_visible=True,remaining_boundary_visible=True),
    semantic_roundtrip=dict(required=True,status='accepted',formalizer='/root',blind_decoder='/root/osd_blind',source_reviewer='/root/source_reviewer',
        verdict=r['verdict'],remaining_semantic_delta='Five DERIVED hinges; conditional empiricalMean convergence explicit. Distinct CONTRACT48/CANARY24/BODY287 audited. Full FINAL remains required. '+boundary),
    graph_contribution=dict(lean_graph='new-node',overview_graph='updated',functor_hypergraph='none-found-with-reason',
        functor_reason='Exact metric/ordinarylimit relation for one already shared FTL process; no categorical/cross-setting transport theorem.',
        focus_targets=names,visual_review='Five whole VALUE witnesses,29 standard-only axiom outputs,24 selected nodes2676 TYPE_VALUEedges16 directVALUEpairs; new site/pixels still pending.',
        edge_semantics='formal-solid; overlays-dashed'),
    progress_updates=dict(teaching_route='updated: one bound sourcecard/fivenotes and exact productionmodule owner; all oldrecords/status/URLs retained',
        banditrlwiki='no-change-with-reason: no Bandit setting modified',results_ledger='updated: five focused compiled candidates, zero accepted untilfullgates; original16/nullretained',
        roadmap='no-change-with-reason: whole16 Goal/globalSGB frontier unchanged',website_surfaces=[p.relative_to(ROOT).as_posix() for p in READERS]),
    truth_boundary=boundary,
    verification=dict(focused_checks=['Five actualbody builds;12 public binarycanaries;5 wholeVALUE/29 standard-only axioms/16 directVALUEpairs/17fences'],
        bandit_check='Combinedroot/Tests/fullharness/both contributorbases/ownshadow pending',site_build='Applicable current local site after combinedgate pending',
        site_check='10959completeoldregistry retention plusfive nodes/currentheaders/originalpixels pending',
        independent_review='Distinct staged CONTRACT48/CANARY24/BODY287 favorable; FINALpending. Reused automated actors, no human/external/runtime attestation.',
        owned_test_files=[CANARY.relative_to(ROOT).as_posix()],owned_test_root_files=['Tests.lean']),
    contributor=dict(name='Codex for Ji Cheng',role='Formalizer, distinct staged automated decoder/source reviewer'))
write(CONTRIBUTION,manifest)
from tools.check_contributor_contract import validate_contract
_,errors=validate_contract(CONTRIBUTION.resolve())
write(RUN/'schema2-validation-v1.json',dict(errors=errors,package_acceptance_pending=True,goal_complete=False))
assert not errors,errors
integrated_fixed()
write(RUN/'reader-integration-bindings-v1.json',dict(public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    body_receipt_sha256=sha(RUN/'public-body-receipt-v1.json'),proposal_sha256=sha(RUN/'reader-proposal-v1.json'),
    old_reader_records_preserved=True,source_card_count_before=18,source_card_count_after=19,new_notes=5,new_module_entries=1,
    combined_full_gates_pending=True,chapter_complete=False,goal_complete=False))
print('Applied exact separately BODY-reviewed root/Test/reader delta; fullgate/FINAL pending.',flush=True)
