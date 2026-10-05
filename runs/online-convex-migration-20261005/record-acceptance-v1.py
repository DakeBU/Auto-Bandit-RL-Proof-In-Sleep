"""Accept only the bounded retained convex source migration after true gates."""
from pathlib import Path
import hashlib,json,subprocess,sys
run=Path(__file__).parent;task='ONLINE-CONVEX-MIGRATION-20261005'
def load(n):return json.loads((run/n).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(n,x):
    with (run/n).open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
r=load('final-reader-receipt-v1.json');assert r['verdict'] in ['accepted','accepted-with-explicit-delta'] and not r['required_repairs']
gate('accepted-binding-audit-v1-01',sys.executable,'-X','utf8',str(run/'verify-accepted-bindings-v1.py'))
audit=load('accepted-binding-audit-v1.json');assert audit['status']=='passed'
freeze=load('draft-freeze-v1.json');ob=load('proof-obligations-proving-v1.json')
ob.update(stage='accepted-local-retained-source-migration',package_accepted=True,chapter_accepted=False,goal_complete=False,new_proofs=0,
    remaining_required=['stacked draft PR delivery','separate finite-loss/domain-intersection consequence','remaining Chapter2 exact contracts/source/migration/chapter gate','Chapter1 legacy source migrations','Chapters3-16/necessary appendix dependencies'])
for x in ob['required']:x.update(state='accepted-local-retained-proof',evidence=['public-body-receipt-v1.json','final-reader-receipt-v1.json','accepted-binding-audit-v1.json'])
write('accepted-obligations-v1.json',ob)
decision=dict(stage='accepted-local',package=task,contract_version=1,retained_public_proofs=22,public_definitions=5,new_proofs=0,canary_modules=4,new_registry_nodes=0,
    all_headers_and_code_tokens_unchanged=True,semantic_verdict=r['verdict'],reviewer='/root/source_reviewer',review_report_sha256=r['report_sha256'],
    binding_audit_sha256=sha(run/'accepted-binding-audit-v1.json'),raw_review_rows_verified=audit['raw_review_rows_verified'],historical_prior_rows=audit['historical_prior_binding_rows_rechecked'],
    source_reader_commit=audit['final_clean_site_commit'],stacked_base='a2728b1da2109844ffec64f594827197cd9b541b',stacked_predecessor_PR=155,
    exact_source_sha256=freeze['primary_sha256'],convention_sha256=freeze['convention_sha256'],
    terminal_progress='Four retained production paths distinctly source/body/reader revalidated; zero new proof body/declaration count. Separate finite-loss endpoint remains mandatory.',
    actual_axiom_names=53,actual_native_safe_guards=22,actual_reused_graph_scope_nodes=27,actual_proof_value_pairs=13,new_graph_export=False,
    shared_registry_scope_nodes=27,old_registry_ids_urls_retained=audit['preserved_old_registry_nodes'],root_jobs=9087,Tests_jobs=9228,full_tests=466,existing_skips=7,
    actual_contributor_production_paths=7,current_main_manifest_missing_paths=16,full_git_diff_check_passed=load('full-diff-v1-01-exit.json')['exit_code']==0,scoped_diff_check_passed=True,
    whitespace_exception=audit['whitespace_exception'],historical_migration_selected_paths=list(freeze['modules']),
    remaining_required=ob['remaining_required'],chapter_2_mandatory_count=None,finite_loss_gap='mandatory-pending-new-contract',
    chapter_complete=False,book_complete=False,goal_complete=False,merged=False,deployed=False,external_human_review=False,external_model_review=False,runtime_model_independently_verified=False)
write('accepted-decision-v1.json',decision)
write('source-inventory-acceptance-overlay-v1.json',dict(schema_version=1,base_inventory='docs/contracts/online-book-v1/source-inventory.json',base_inventory_raw_sha256=sha('docs/contracts/online-book-v1/source-inventory.json'),
    preserves_historical_inventory_raw=True,source_sha256=freeze['primary_sha256'],accepted_named_endpoints=freeze['headers'],
    anchors=['Def2.2','Def2.3','Thm2.4','Examples2.5/2.6','named domain convexity/indicator equivalence/indicator-addition convexity','four closure rules with explicit upperAdd interpretation'],
    finite_loss_domain_intersection_consequence='still mandatory; not covered by this acceptance',evidence=(run/'accepted-decision-v1.json').as_posix(),new_proofs=0,merged=False,live=False,chapter_2_mandatory_count=None,chapter_2_accepted=False,whole_book_goal='active'))
write('contribution-acceptance-overlay-v1.json',dict(manifest='research-wiki/contribution-contracts/'+task+'.json',manifest_sha256=sha('research-wiki/contribution-contracts/'+task+'.json'),candidate_manifest_raw_preserved=True,
    semantic_verdict=r['verdict'],graph='compiled-dependencies-v1.json',new_graph_export=False,registry='registry-final02.json',site='site-final02-check-exit.json',reader='final-reader-receipt-v1.json',immutable='accepted-binding-audit-v1.json',production_paths=7,contributor_contracts=1,package_accepted_local=True,chapter_accepted=False,book_accepted=False))
write('program-milestone-v1.json',dict(package=task,status='accepted-local; stacked draft PR pending',chapter=2,selected_historical_migration_paths=4,new_proofs=0,
    chapter_2_status='partial',chapter_2_mandatory_count=None,finite_loss_domain_intersection='mandatory-pending-new-contract',
    numbered_navigation_entries=32,algorithm_boxes=2,unnumbered_audit_groups=18,enumeration_is_not_frozen_target_count=True,chapter_2_accepted=False,
    remaining_original26_historical_semantic_migrations=19,remaining_main_manifest_missing_paths=16,future_chapters='3-16 unenumerated mandatory; null is not zero',whole_book_goal='active',main_updated=False,live_updated=False))
write('memory-digest-accepted-v1.md','Four retained convex modules22 proofs/five definitions accepted locally with distinct contract/body/final-reader reviews, zero new proof/registry nodes. Exact infinity/real-height/noBottom/domain/strict-weight/real-composition/upperAdd attributed interpretation boundaries retained. Three reader corrections addressed. Separate finite-loss/domain-intersection consequence mandatory and visible, not covered by this package. Four canaries freshly elaborated,53 named standard3-or-none axioms/22 guards/root9087/Tests9228/full466/7 passed. Reused graph27nodes13value pairs, no new export; shared registry27 actual nodes and every old ID/URL retained. Raw originals and explicit historical snapshot chains preserve fixed reviews; the refreshed first UNFROZEN history-audit JSON limitation disclosed. Whole Goal active, Chapter2 totalnull, standalone exercises optional/main formal results mandatory. Stacked draft PR pending; no main/live/merge/deploy/human/external review.')
write('retrieval-index-accepted-v1.md','Reuse four modules:OnlineConvexExtended/Examples/Closures/Sums and shared BanditRL.OnlineConvex definitions. Frozen22 actual native headers/source/convention/context/DAG:docs/contracts/online-convex-migration-v1. Current actual body/canary/53 axioms/22 guards:public-actual-bindings-v1.json. Separate contract/body/final-reader receipts plus accepted-binding-audit-v1.json, explicit original snapshots/historical-chain v2 audit. Actual graph reuse27nodes13pairs and same canonical registry-final02.json. Next ready source leaf:finite-loss/domain-of-constrained-sum intersection, currently only proposed mandatory gap, not frozen/proved. Then remaining first-order/optimality/Jensen and Chapter1 legacy source/migration audit before complete Chapter2 gate or Chapter3 proof writing.')
gate('accepted-reviewer-trial-v1',sys.executable,'-X','utf8','tools/bandit.py','trial-log','--task',task,'--run-id',run.name,'--role','reviewer','--kind','review','--status','accepted','--attempt-id','RETAINED-CONVEX22-V1','--reviewer-validated','--progress-class','retrieval-reuse','--reused-declaration','BanditRL.OnlineConvex.convex_nonneg_linear_combination','--verifier-evidence',str(run/'accepted-decision-v1.json'),'--notes','Distinct final source/reader/bindings accept four retained modules22 proofs, zero new bodies. Integrated/full/shared registry/site passed; finite-loss endpoint/chapter/book still mandatory, stacked PR pending.')
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
with (run/'accepted-scoped-trials-v1.jsonl').open('w',encoding='utf-8',newline='\n') as f:
    for t in trials:
        if t.get('task')==task:f.write(json.dumps(t)+'\n')
leaf=load('candidate-frontier-v1.json')['current_leaf']
gate('accepted-frontier-refresh-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16 Goal; retained convex package accepted only, finite-loss endpoint/Chapter2/book incomplete','--leaf',task,'--kind','lean','--statement',leaf['statement'],'--declaration',leaf['declaration'],'--file',leaf['file'],'--source-status','accepted','--leaf-status','accepted','--dependency','lean:BanditRL.OnlineConvex.convex_upperAdd:compiled','--dependency','lean:BanditRL.OnlineConvex.convex_nonneg_mul:compiled','--dependency','review:final-reader:accepted','--dependency','harness:full-bandit:passed','--trials',str(run/'accepted-scoped-trials-v1.jsonl'),'--output',str(run/'accepted-frontier-v1.json'),'--shadow-status','pending')
gate('accepted-frontier-shadow-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow','--trials',str(run/'accepted-scoped-trials-v1.jsonl'),'--memory-digest',str(run/'memory-digest-accepted-v1.md'),'--frontier',str(run/'accepted-frontier-v1.json'))
gate('accepted-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','accepted','--payload-json',json.dumps(dict(run_id=run.name,contract_version=1,scope='four retained convex production modules only',retained_proofs=22,new_proofs=0,canary_modules=4,semantic_verdict=r['verdict'],raw_rows=audit['raw_review_rows_verified'],finite_loss_gap='mandatory',chapter_complete=False,book_complete=False,goal_complete=False,merged=False,deployed=False)))
print('Bounded retained convex package accepted locally only; finite-loss/whole Goal remain active; draft PR delivery still required.')
