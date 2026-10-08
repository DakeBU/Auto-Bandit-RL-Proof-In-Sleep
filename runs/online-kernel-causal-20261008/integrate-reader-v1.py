from common_body_v1 import *

r = body_fixed()
proposal = load(RUN/'reader-proposal-v1.json')
names = [t['name'] for t in load(RUN/'stabilized-contract-v1.json')['targets']]
for rel,addition in r['approved_future_exact_scope']['exact_root_additions'].items():
    p = ROOT/rel
    assert p.read_bytes() == baseline(rel)
    p.write_bytes(p.read_bytes()+addition.encode('utf8'))
for label in ['readings','highlights','chapters']:
    p = ROOT/'website/content'/(label+'.json')
    data = load(p)
    if label == 'highlights':
        assert not any(x['full_name'] in names for x in data[label])
        data[label] += proposal['notes']
    else:
        row = next(x for x in data[label] if x['slug'] == ROUTE)
        if label == 'readings':
            row['source_theorems'].append(proposal['card'])
        else:
            for k in ['completion_blockers','open_gaps']:
                row[k].append(proposal['boundary'])
            row['module_globs'].append(PUBLIC.relative_to(ROOT).as_posix())
    p.write_bytes((json.dumps(data,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
boundary = proposal['boundary']
manifest = dict(schema_version='2.0',id=TASK,route='online-learning/chapter-1',frontier_cell=ROUTE,source_facing=True,
    source=dict(kind='book',title='Online Learning: A Modern Introduction Using Convex Optimization',
      version='arXiv:1912.13213v10,2026-06-21; SHA '+PDF_SHA,
      anchor='Five derived behavioral-kernel realization endpoints, printed1/PDF13 and printed3/PDF15',
      url='https://arxiv.org/pdf/1912.13213v10'),
    target='One family, actual causal recursion, derived joint/conditional laws and same-process every-horizon IID expected-fixed excess. '+boundary,
    affected_files=[PUBLIC.relative_to(ROOT).as_posix(),'BanditRLProof.lean']+[p.relative_to(ROOT).as_posix() for p in READERS],
    declarations=names,
    reuse_plan=dict(classification='adapt',decision='adapt_existing',
      searched_existing=['Pinned Mathlib Representation/CondDistrib/InfinitePi/compProd signatures and actual shared private-seed/IID producer; native retrieval and compiled VALUE audit.'],
      reused_declarations=['ProbabilityTheory.Kernel.exists_measurable_map_eq_unitInterval',
        'ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd',
        'BanditRL.OnlineLearning.independent_private_seed_pair',
        'BanditRL.OnlineLearning.randomized_history_policy_expectedFixed_excess'],
      new_shared_declarations=names,known_consumers=names[2:],
      planned_consumers=['Required precise source/protocol information audit and chapter integration'],
      no_duplicate_wrapper=True,
      decision_reason='Reuse existing single-step sampling and IID producer, add actual finite causal recursion and fresh-draw law compatibility. Private generic product-map helper is a mathlib-candidate; transparent conditional-law adapter connects the public chain.'),
    reader_contract=dict(source_anchor_visible=True,natural_language_formula_proof=True,hidden_assumptions_visible=True,
      source_vs_lean_delta_visible=True,lean_folded=True,dependencies_visible=True,remaining_boundary_visible=True),
    semantic_roundtrip=dict(required=True,status='accepted',formalizer='/root',blind_decoder='/root/osd_blind',
      source_reviewer='/root/source_reviewer',verdict=r['verdict'],
      remaining_semantic_delta='Distinct CONTRACT104, retrieval supplement16 and BODY350 accept the explicit derived behavioral-kernel/exogenous-law scope. R1-R7 FINAL remains pending. '+boundary),
    graph_contribution=dict(lean_graph='integration-node',overview_graph='updated',functor_hypergraph='none-found-with-reason',
      functor_reason='Actual causal realization inside the specified guessing-game model; no categorical or independent-setting composition claim.',
      focus_targets=names,
      visual_review='Actual complete five VALUE witnesses,57 standard-only axiom outputs,22 required direct VALUE pairs; current shared Book/site/original pixels pending.',
      edge_semantics='formal-solid; overlays-dashed'),
    progress_updates=dict(teaching_route='updated: own bound source card/five notes/exact module ownership, all old entries/statuses/links preserved',
      banditrlwiki='no-change-with-reason: no Bandit setting altered',
      results_ledger='updated: five compiled derived candidates, zero accepted until full gates; original16/null retained',
      roadmap='no-change-with-reason: whole16 Goal and global SGB frontier preserved',
      website_surfaces=[p.relative_to(ROOT).as_posix() for p in READERS]),
    truth_boundary=boundary,
    verification=dict(focused_checks=['Five actual focused bodies;13 public stochastic/history-feedback canaries;5 whole VALUE witnesses/57 standard-only axiom outputs/22 directVALUEpairs/5 fences'],
      bandit_check='Combined root/Tests/fullharness/both contributor bases/own shadow pending',
      site_build='Applicable clean local site after combined gate pending',
      site_check='Old shared registry preservation/five exact headers/original rendered math and browser pixels pending',
      independent_review='Distinct staged CONTRACT104/BODY350 accepted-with-explicit-delta, retrieval16 independently verified. R1-R7 FINAL pending; reused automated history, no absolute blind/human/external/runtime attestation.',
      owned_test_files=[CANARY.relative_to(ROOT).as_posix()],owned_test_root_files=['Tests.lean']),
    contributor=dict(name='Codex for Ji Cheng',role='Formalizer, distinct staged automated decoder/source reviewer'))
write(CONTRIBUTION,manifest)
from tools.check_contributor_contract import validate_contract
_,errors = validate_contract(CONTRIBUTION.resolve())
write(RUN/'schema2-validation-v1.json',dict(errors=errors,contract_body_only=True,final_pending=True,goal_complete=False))
assert not errors, errors
write(RUN/'reader-integration-bindings-v1.json',dict(proposal_sha256=sha(RUN/'reader-proposal-v1.json'),
    body_receipt_sha256=sha(RUN/'public-body-receipt-v1.json'),public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    new_source_cards=1,new_notes=5,exact_one_module_globs_addition=True,
    old_reader_entries_preserved=True,combined_gates_pending=True))
fixed_integrated()
print('Exact reviewed root/Test and shared Book reader integration complete; combined/FINAL gates pending.',flush=True)
