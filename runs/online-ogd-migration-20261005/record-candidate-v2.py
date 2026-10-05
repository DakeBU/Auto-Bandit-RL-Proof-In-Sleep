"""Record actual candidate evidence without claiming pending package gates."""
from pathlib import Path
import hashlib,json,subprocess,sys
run=Path(__file__).parent
task='ONLINE-OGD-MIGRATION-20261005'
def load(n):return json.loads((run/n).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,v):
    p=Path(p);p.parent.mkdir(parents=True,exist_ok=True)
    with p.open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(v,str):f.write(v+'\n')
        else:json.dump(v,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):
    subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
bindings=load('public-actual-bindings-v2.json');review=load('public-body-receipt-v2.json')
assert sha('BanditRLProof/OnlineGradientDescentSource.lean')==bindings['public_module_sha256']
assert sha('Tests/OnlineGradientDescentSourceCanary.lean')==bindings['public_canary_sha256']
assert review['verdict']=='accepted-with-explicit-delta' and not review['required_repairs']
assert sha(run/'public-body-review-v2.md')==review['report_sha256']
inventory=load('public-named-declarations-v2.json')
decls=inventory['new_public']+inventory['old_reused'];assert len(decls)==38
graph=load('compiled-dependencies-v2.json');assert graph['status']=='passed'
for label in ['root-v2-01','Tests-v2-01','public-canary-v2-01','public-axioms-v2-01','prepare-public-gates-v2-01','graph-verify-v2-01']:
    assert load(label+'-exit.json')['exit_code']==0,label
pending=['full harness','clean shared registry/site build and check','final source reader review',
         'immutable binding audit','exact stacked contributor gate','stacked draft PR delivery']
manifest=dict(schema_version='2.0',id=task,route='online-learning/chapter-2',frontier_cell='online-ogd',source_facing=True,
    source=dict(kind='book',title='Online Learning: A Modern Introduction Using Convex Optimization',
        version='arXiv:1912.13213v10, 21 June 2026; SHA256 cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17',
        anchor='Algorithm2.1, Proposition2.11, Lemma2.12, Theorem2.13 fixed/variable and Equation2.1; printed12–15 / PDF24–27; source game printed8 / PDF20',url='https://arxiv.org/pdf/1912.13213v10'),
    target='Repair source regularity using the same projected causal OGD recurrence; both one-step inequalities, sharp fixed/variable terminals and tuned DGsqrtT; independently audit retained old statements.',
    affected_files=['BanditRLProof.lean','BanditRLProof/OnlineGradientDescent.lean','BanditRLProof/OnlineGradientDescentVariable.lean',
        'BanditRLProof/OnlineGradientDescentSource.lean','Tests.lean','Tests/OnlineGradientDescentSourceCanary.lean',
        'website/content/chapters.json','website/content/readings.json','website/content/highlights.json'],
    declarations=decls,
    reuse_plan=dict(classification='adapt',decision='adapt_existing',
        searched_existing=['Actual mathlib projection and gradient declaration retrieval; native type probes and old body audits retained in this run.'],
        reused_declarations=['exists_norm_eq_iInf_of_complete_convex','norm_eq_iInf_iff_real_inner_le_zero',
            'BanditRL.OnlineConvex.convex_gradient_lower_bound','BanditRL.OnlineGradientDescent.lemma_2_12',
            'BanditRL.OnlineGradientDescent.iterate_mem','BanditRL.OnlineGradientDescent.iterateVariable_mem',
            'BanditRL.OnlineGradientDescent.weighted_potential_sum'],
        new_shared_declarations=inventory['new_public'],known_consumers=inventory['canary'],
        planned_consumers=['Complete Chapter2 source audit and subsequent chapters in the shared graph.'],
        no_duplicate_wrapper=True,decision_reason='New source-facing regularity predicates feed existing Domain/project/step/iterate recurrences; no per-book project or duplicated algorithm.'),
    reader_contract={k:True for k in ['source_anchor_visible','natural_language_formula_proof','hidden_assumptions_visible',
        'source_vs_lean_delta_visible','lean_folded','dependencies_visible','remaining_boundary_visible']},
    semantic_roundtrip=dict(required=True,status='accepted',formalizer='/root',blind_decoder='/root/normal_blind',
        source_reviewer='/root/source_reviewer',verdict=review['verdict'],
        remaining_semantic_delta='Distinct contract and actual body/canary reviews accepted with explicit supplied ambient extension and complete-Hilbert generalization. Final reader and package gates separately pending; no human/external review.'),
    graph_contribution=dict(lean_graph='new-node',overview_graph='updated',functor_hypergraph='none-found-with-reason',
        functor_reason='Same shared projected learner with repaired source interface; no separately certified functor.',
        focus_targets=decls,visual_review='Actual compiled graph verified:38 explicit nodes and33 required proof-value pairs. Reader/site review pending.',edge_semantics='formal-solid; overlays-dashed'),
    progress_updates=dict(teaching_route='updated:14 new shared declaration nodes,5 source cards,old URLs retained; Chapter2 incomplete.',
        banditrlwiki='no-change-with-reason: no new Bandit setting.',results_ledger='no-change-with-reason: existing Bandit results unchanged; additive Online acceptance overlays follow gates.',
        roadmap='no-change-with-reason: persistent whole-book Goal active; global SGB frontier untouched.',
        website_surfaces=['website/content/chapters.json','website/content/readings.json','website/content/highlights.json']),
    truth_boundary='Supplied ambient extension on arbitrary open U containing V; convexity only on V. No extension existence or extension-independent gradient is claimed for thin V. Old RegularLoss assumes convexity on an open neighborhood and remains a valid stronger interface; old16 statements/bodies independently reviewed without rewriting historical contracts. Fixed terminal needs no bounded V and includes T0 cancellation. Variable terminal needs positive nonincreasing finite-prefix eta and T>=1, uses eta(T-1), allows zero diameter. Tuned D,G,T positive and gradient bounds refer to the same actual tuned run. The max-exp canary proves one open U is nonconvex, not that every alternative convex open U is impossible. Deterministic pathwise bound only; no randomized-law claim. Two historical OGD files audited here; remaining historical production migration and full Chapter2 enumeration remain mandatory. Local compilation/stacked PR do not update main/live.',
    verification=dict(focused_checks=['12 actual public proofs,2 definitions,30 public canary theorems,75 unique actual #check/#print axioms standard-or-none,12 actual public safe-fence checks.'],
        bandit_check='Combined root9087jobs and Tests9228jobs passed; complete tools/bandit.py check pending.',
        site_build='lean-verified only after applicable full Lean/harness gate; generated_site untouched.',
        site_check='Clean registry/reader/final immutable gates pending.',independent_review='Distinct required automated semantic actors, requested Astra/medium; runtime model not independently attested; no human/external review.'),
    contributor=dict(name='Codex for Ji Cheng',role='Formalizer/integrator with distinct required automated semantic actors; source attribution retained'))
write('research-wiki/contribution-contracts/'+task+'.json',manifest)
obligations=load('proof-obligations-current-v2.json')
obligations.update(stage='candidate',public_proofs=12,public_definitions=2,canary_theorems=30,actual_axiom_names=75,
    package_accepted=False,chapter_accepted=False,book_accepted=False,goal_complete=False,remaining_gates=pending)
for row in obligations['required']:
    row.update(state='source-body-reviewed-candidate',evidence=row.get('evidence',[])+['public-body-receipt-v2.json','public-actual-bindings-v2.json'])
write(run/'candidate-obligations-v2.json',obligations)
decision=dict(stage='candidate',package=task,contract_version=2,source_body_verdict=review['verdict'],
    reviewer_report_sha256=review['report_sha256'],public_proofs=12,public_definitions=2,canary_theorems=30,
    old_independently_reviewed_theorems=16,old_code_tokens_unchanged=True,axiom_names=75,root_jobs=9087,Tests_jobs=9228,
    actual_graph_scope_nodes=38,required_proof_value_pairs=len(graph['required_proof_value_checks']),
    terminal_progress='Actual source-to-feasible adapter closes both one-step bounds and sharp fixed/variable/tuned terminals for the same learner.',
    historical26_selected_production_paths=2,historical_other24_not_accepted_by_this_receipt=True,
    source_inventory_reconciliation='Prop2.11/Lemma2.12 still historical draft; accepted overlay only after gates.',
    remaining_gates=pending,package_accepted=False,chapter_complete=False,book_complete=False,goal_complete=False,merged=False,deployed=False)
write(run/'candidate-decision-v2.json',decision)
write(run/'memory-digest-candidate-v2.md','OGD source repair candidate:12 frozen actual proofs/2 predicates,30 canaries,75 actual named axioms,12 native public safe fences,root9087/Tests9228 and compiled38-node graph/33 proof-value pairs passed. v1 rejected over-strong source coverage; v2 distinct contract/body review accepted with supplied ambient extension and no extension-independence claim. Old16 bodies remain unchanged and valid under stronger interface. Same causal recurrence, actual projected steps, both single-step inequalities, negative fixed/variable terminal, tuned positive DGT. Full harness, clean registry/site, final reader, immutable bindings, contributor gate and stacked PR pending. Chapter2/book incomplete; historical other24 production paths remain mandatory; global SGB unchanged; whole Goal active; no main/live claim.')
write(run/'retrieval-index-candidate-v2.md','Actual shared projection API, convex_gradient_lower_bound, genuine Riesz-linear loss gradient and existing affine-instance lemma, iterate feasibility, weighted_potential_sum. Actual proof-value graph:compiled-dependencies-v2.json. Public frozen headers/axioms:public-actual-bindings-v2.json; source/body receipts independent. Historical raw receipts resolve only to exact authorized pre-integration snapshots, never silently to later live bytes. Next:full harness and reader/immutable/site gates, then remaining historical migration/full Chapter2 enumeration.')
gate('candidate-reviewer-trial-v2',sys.executable,'-X','utf8','tools/bandit.py','trial-log','--task',task,'--run-id',run.name,
    '--role','reviewer','--kind','review','--status','compiled','--reviewer-validated','--progress-class','closed-frontier',
    '--attempt-id','ONLINE-OGD-SOURCE12-BODY-V2','--verifier-evidence',str(run/'candidate-decision-v2.json'),
    '--notes','Actual12 public bodies/30 canaries/75axioms/root9087Tests9228/38graph accepted by distinct source-body review; package/chapter/book incomplete; pending full harness/site/final reader/immutable/PR.')
gate('candidate-lifecycle-v2',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','candidate',
    '--payload-json',json.dumps(dict(run_id=run.name,contract_version=2,scope='OGD source repair only',public_proofs=12,
        canaries=30,axioms=75,root_jobs=9087,Tests_jobs=9228,remaining_gates=pending,chapter_complete=False,book_complete=False,goal_complete=False)))
print('Recorded actual candidate; full harness/site/final reader/immutable/contributor/PR still pending.')
