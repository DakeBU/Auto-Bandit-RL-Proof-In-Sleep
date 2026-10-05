"""Record this retained-source package only after final review and byte audit."""
from pathlib import Path
import hashlib,json,subprocess,sys
run=Path(__file__).parent;task='ONLINE-FTL-MIGRATION-20261005'
def load(n):return json.loads((run/n).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(n,x):
    with (run/n).open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
review=load('final-reader-receipt-v1.json')
assert review['verdict']=='accepted-with-explicit-delta' and not review['required_repairs']
gate('accepted-binding-audit-v1-01',sys.executable,'-X','utf8',str(run/'verify-accepted-bindings-v1.py'))
audit=load('accepted-binding-audit-v1.json');assert audit['status']=='passed'
ob=load('proof-obligations-proving-v1.json')
ob.update(stage='accepted-local-retained-source-migration',package_accepted=True,chapter_accepted=False,
    goal_complete=False,new_proofs=0,remaining_package_gates=['stacked draft PR delivery'])
for r in ob['required']:r.update(state='accepted-local-retained-proof',evidence=['public-body-receipt-v1.json','final-reader-receipt-v1.json','accepted-binding-audit-v1.json'])
write('accepted-obligations-v1.json',ob)
decision=dict(stage='accepted-local',package=task,contract_version=1,retained_public_proofs=7,public_definitions=3,
    new_proofs=0,canary_proofs=2,new_registry_nodes=0,all_headers_and_code_tokens_unchanged=True,
    semantic_verdict=review['verdict'],reviewer='/root/source_reviewer',review_report_sha256=review['report_sha256'],
    binding_audit_sha256=sha(run/'accepted-binding-audit-v1.json'),raw_review_rows_verified=audit['raw_review_rows_verified'],
    source_reader_commit=audit['final_clean_site_commit'],stacked_base='4b55f5ebebb370ebe9e173b9bf5155b97a2e3998',stacked_predecessor_PR=154,
    exact_source_sha256='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17',
    terminal_progress='Retained exact causal FTL source terminal independently revalidated; no new proof body or mathematical declaration count.',
    actual_axiom_names=12,actual_native_safe_guards=7,actual_reused_graph_scope_nodes=10,actual_proof_value_pairs=6,new_graph_export=False,
    shared_registry_scope_nodes=10,old_registry_ids_urls_retained=audit['preserved_old_registry_nodes'],
    root_jobs=9087,Tests_jobs=9228,full_tests=466,existing_skips=7,actual_contributor_production_paths=4,
    full_git_diff_check_passed=False,scoped_diff_check_passed=True,whitespace_exception=audit['whitespace_exception'],
    historical_migration_selected_paths=['BanditRLProof/OnlineFTLFailure.lean'],
    current_main_contributor_missing_paths=20,historical_other23_of_original26_semantic_migrations_not_accepted_here=True,
    remaining_required=['stacked draft PR delivery','remaining historical production source/contribution migration',
        'full Chapter2 exact numbered/unnumbered signature and chapter gate','Chapter1 legacy source migration',
        'Chapters3-16 and required appendix dependencies'],
    chapter_complete=False,book_complete=False,goal_complete=False,merged=False,deployed=False,
    external_human_review=False,external_model_review=False,runtime_model_independently_verified=False)
write('accepted-decision-v1.json',decision)
write('source-inventory-acceptance-overlay-v1.json',dict(schema_version=1,
    base_inventory='docs/contracts/online-book-v1/source-inventory.json',base_inventory_raw_sha256=sha('docs/contracts/online-book-v1/source-inventory.json'),
    preserves_historical_inventory_raw=True,source_sha256=decision['exact_source_sha256'],
    updates=[dict(source_id='Example 2.10',printed_page=12,pdf_page=24,lean_name='BanditRL.OnlineLearning.example_2_10',
        status='accepted-local-retained-source-migration',evidence=(run/'accepted-decision-v1.json').as_posix(),new_proofs=0,merged=False,live=False)],
    chapter_2_mandatory_count=None,chapter_2_accepted=False,whole_book_goal='active'))
write('contribution-acceptance-overlay-v1.json',dict(manifest='research-wiki/contribution-contracts/'+task+'.json',
    manifest_sha256=sha('research-wiki/contribution-contracts/'+task+'.json'),candidate_manifest_raw_preserved=True,
    semantic_verdict=review['verdict'],graph='compiled-dependencies-v1.json',new_graph_export=False,
    registry='registry-final01.json',site='site-final01-check-exit.json',reader='final-reader-receipt-v1.json',
    immutable='accepted-binding-audit-v1.json',production_paths=4,contributor_contracts=1,
    package_accepted_local=True,chapter_accepted=False,book_accepted=False))
write('program-milestone-v1.json',dict(package=task,status='accepted-local; draft PR pending',chapter=2,
    current_source_overlay='source-inventory-acceptance-overlay-v1.json',chapter_2_status='partial',chapter_2_mandatory_count=None,
    numbered_navigation_entries=32,algorithm_boxes=2,unnumbered_audit_groups=18,enumeration_is_not_frozen_target_count=True,
    chapter_2_accepted=False,selected_historical_migration_paths=1,remaining_main_manifest_missing_paths=20,
    remaining_original26_historical_semantic_migrations=23,future_chapters='3-16 unenumerated and mandatory; null is not zero obligations',
    whole_book_goal='active',main_updated=False,live_updated=False))
write('memory-digest-accepted-v1.md','Retained FTL Example2.10 source migration accepted locally:7 old proofs/3 definitions, zero new proof/registry nodes. Exact actual comparator0 regret T-1-x0/2 >=T-3/2 for every feasible fixed x0,T>=1; source0-based shift, concrete generic ties and separate initial feasibility explicit. Distinct contract/body/final-reader reviews and exact raw audits passed. Two reader formulas repaired. Public COMMENT only; all old headers/code tokens and canary bytes unchanged, raw snapshots preserve current/prior OGD receipts. Actual12 standard-or-none axiom outputs/7 safe guards/root9087/Tests9228/full466/7 passed; first full harness boundary-string failure preserved/repaired without changing tests. Reused actual graph10 scope/6 required value pairs, no new export. Clean site477d8e2c and registry10 original nodes/10804 old IDsURLs retained, actual first viewport observed. Raw whitespace failure preserved with scoped log/exact-snapshot exceptions only. Exact stacked contributor4paths/one contract passed; main20missing and other23oforiginal26 semantic audits mandatory. Whole Goal ACTIVE, Chapter2 mandatory_totalnull; fresh34 navigation anchors/18unnumberedgroups are draft, not52 accepted targets. DraftPR pending; no main/live/merge/deploy/human/external review.')
write('retrieval-index-accepted-v1.md','Reuse BanditRL.OnlineLearning.prefixCoefficient/linearFTLPredict/failureCoefficient and their seven actual proof bodies; public terminal example_2_10. Actual named canaries:six_rounds/actual_predictions. Frozen header/context/source:docs/contracts/online-ftl-migration-v1. Separate source/body/final receipts and accepted-binding-audit-v1.json. Actual proof-term graph:ready-dependencies-v1.json/compiled-dependencies-v1.json; source inventory overlay and same shared registry-final01.json. Next dependency-ready source migration:convex extended/closure/sum primitives and exact first-order/optimality/Jensen interfaces; source numbered/unnumbered remaining-contract-audit-v1.md, no Chapter3 proof writing beforeChapter2 gate.')
gate('accepted-reviewer-trial-v1',sys.executable,'-X','utf8','tools/bandit.py','trial-log','--task',task,'--run-id',run.name,
    '--role','reviewer','--kind','review','--status','accepted','--attempt-id','RETAINED-FTL-SOURCE7-V1',
    '--reviewer-validated','--progress-class','retrieval-reuse','--reused-declaration','BanditRL.OnlineLearning.example_2_10',
    '--verifier-evidence',str(run/'accepted-decision-v1.json'),
    '--notes','Distinct final reader and raw binding audit accept one retained FTL source path. Seven proofs reused, zero new bodies; full466/7 and same shared registry/site passed. Chapter/book incomplete, stacked PR pending.')
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
with (run/'accepted-scoped-trials-v1.jsonl').open('w',encoding='utf-8',newline='\n') as f:
    for t in trials:
        if t.get('task')==task:f.write(json.dumps(t)+'\n')
leaf=load('candidate-frontier-v1.json')['current_leaf']
gate('accepted-frontier-refresh-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh',
    '--root-objective','Persistent Orabona Chapters1-16 Goal; retained FTL source package accepted only, Chapter2/book incomplete',
    '--leaf',task,'--kind','lean','--statement',leaf['statement'],'--declaration',leaf['declaration'],'--file',leaf['file'],
    '--source-status','accepted','--leaf-status','accepted','--dependency','lean:BanditRL.OnlineLearning.failure_prediction:compiled',
    '--dependency','review:final-reader:accepted','--dependency','harness:full-bandit:passed',
    '--trials',str(run/'accepted-scoped-trials-v1.jsonl'),'--output',str(run/'accepted-frontier-v1.json'),'--shadow-status','pending')
gate('accepted-frontier-shadow-v1',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow',
    '--trials',str(run/'accepted-scoped-trials-v1.jsonl'),'--memory-digest',str(run/'memory-digest-accepted-v1.md'),
    '--frontier',str(run/'accepted-frontier-v1.json'))
gate('accepted-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','accepted',
    '--payload-json',json.dumps(dict(run_id=run.name,contract_version=1,scope='one retained FTL source package only',
        retained_proofs=7,new_proofs=0,canaries=2,semantic_verdict=review['verdict'],raw_rows=audit['raw_review_rows_verified'],
        chapter_complete=False,book_complete=False,goal_complete=False,merged=False,deployed=False)))
print('Retained FTL source package accepted locally only; whole Goal ACTIVE; stacked draft PR delivery still required.')
