"""Record local OGD package acceptance only after distinct reader and immutable audit."""
from pathlib import Path
import hashlib,json,subprocess,sys
run=Path(__file__).parent;task='ONLINE-OGD-MIGRATION-20261005'
def load(n):return json.loads((run/n).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(n,x):
    with (run/n).open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
review=load('final-reader-receipt-v2.json')
assert review['verdict']=='accepted-with-explicit-delta' and not review['required_repairs']
gate('accepted-binding-audit-v2-01',sys.executable,'-X','utf8',str(run/'verify-accepted-bindings-v2.py'))
audit=load('accepted-binding-audit-v2.json');assert audit['status']=='passed'
obligations=load('candidate-obligations-v2.json')
obligations.update(stage='accepted-local',package_accepted=True,chapter_accepted=False,book_accepted=False,
    goal_complete=False,remaining_gates=['stacked draft PR delivery'])
for row in obligations['required']:
    row.update(state='accepted-local',evidence=row['evidence']+['final-reader-receipt-v2.json','accepted-binding-audit-v2.json'])
write('accepted-obligations-v2.json',obligations)
decision=dict(stage='accepted-local',package=task,contract_version=2,public_proofs=12,public_definitions=2,
    old_independently_reviewed_theorems=16,old_context_declarations=8,old_headers_and_all_code_tokens_unchanged=True,
    canary_theorems=30,canary_definitions_and_alias=7,actual_axiom_names=75,actual_safe_fences=12,
    semantic_verdict=review['verdict'],reviewer='/root/source_reviewer',review_report_sha256=review['report_sha256'],
    binding_audit_sha256=sha(run/'accepted-binding-audit-v2.json'),raw_review_rows_verified=audit['raw_review_rows_verified'],
    source_reader_commit=audit['final_clean_site_commit'],stacked_base='64e25407a4a2b952fa4597d6c2cffc8df16810e8',
    exact_source_sha256='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17',
    terminal_progress='Actual arbitrary-open source adapter, both same-step inequalities, same-run sharp fixed/variable telescopes and tuned DGsqrtT are closed. Original historical contracts/proofs unchanged.',
    graph_scope_nodes=38,actual_proof_value_pairs=33,new_shared_registry_nodes=14,old_registry_ids_urls_retained=10790,
    root_jobs=9087,Tests_jobs=9228,full_tests=466,existing_skips=7,actual_contributor_production_paths=7,
    full_git_diff_check_passed=False,scoped_diff_check_passed=True,whitespace_exception=audit['whitespace_exception'],
    historical_migration_selected_paths=['BanditRLProof/OnlineGradientDescent.lean','BanditRLProof/OnlineGradientDescentVariable.lean'],
    current_main_contributor_missing_paths=21,historical_other24_semantic_migration_not_accepted_by_this_receipt=True,
    remaining_required=['stacked draft PR delivery','remaining historical production independent semantic/contribution migration',
        'complete Chapter2 numbered/unnumbered source enumeration and chapter gate','Chapters3-16 and necessary appendix dependencies'],
    chapter_complete=False,book_complete=False,goal_complete=False,merged=False,deployed=False,
    external_human_review=False,external_model_review=False,runtime_model_independently_verified=False)
write('accepted-decision-v2.json',decision)
new='BanditRL.OnlineGradientDescentSource.';old='BanditRL.OnlineGradientDescent.'
updates=[dict(source_id='Algorithm 2.1',printed_page=12,pdf_page=24,lean_names=[old+'Domain',old+'project',old+'step',old+'iterate',old+'iterateVariable',old+'iterate_mem',old+'iterate_prefix',old+'iterateVariable_mem',old+'iterateVariable_prefix']),
    dict(source_id='Proposition 2.11',printed_page=12,pdf_page=24,lean_name=old+'proposition_2_11'),
    dict(source_id='Lemma 2.12',printed_page=13,pdf_page=25,lean_name=new+'lemma_2_12',source_conversion=new+'source_to_feasible'),
    dict(source_id='Theorem 2.13',printed_page=13,pdf_page=25,lean_names=[new+'theorem_2_13_fixed',new+'theorem_2_13_variable'],source_conversion=new+'source_to_feasible',historical_stronger_names=[old+'theorem_2_13_fixed',old+'theorem_2_13_variable']),
    dict(source_id='Equation (2.1)',printed_page=15,pdf_page=27,lean_name=new+'equation_2_1',source_conversion=new+'source_to_feasible')]
for r in updates:r.update(status='accepted-local',evidence=(run/'accepted-decision-v2.json').as_posix(),merged=False,live=False)
write('source-inventory-acceptance-overlay-v2.json',dict(schema_version=1,
    preserves_historical_source_inventory_raw=True,base_inventory='docs/contracts/online-book-v1/source-inventory.json',
    base_inventory_raw_sha256=sha('docs/contracts/online-book-v1/source-inventory.json'),
    source_sha256=decision['exact_source_sha256'],updates=updates,
    source_semantics='Supplied ambient extension on arbitrary open U; convexity on V. No extension existence/independence claim. Complete-Hilbert generalization explicitly retained.',
    chapter_2_mandatory_count=None,chapter_2_accepted=False,whole_book_goal='active'))
write('contribution-acceptance-overlay-v2.json',dict(manifest='research-wiki/contribution-contracts/'+task+'.json',
    manifest_sha256=sha('research-wiki/contribution-contracts/'+task+'.json'),candidate_manifest_raw_preserved=True,
    semantic_roundtrip=review['verdict'],graph='compiled-dependencies-v2.json',registry='registry-final02.json',
    site='site-final02-check-exit.json',reader='final-reader-receipt-v2.json',immutable='accepted-binding-audit-v2.json',
    production_paths=7,contributor_contracts=1,package_accepted_local=True,chapter_accepted=False,book_accepted=False))
write('program-milestone-v2.json',dict(package=task,status='accepted-local; draft PR pending',chapter=2,
    historical_source_inventory_preserved=True,current_source_overlay='source-inventory-acceptance-overlay-v2.json',
    chapter_2_status='partial',chapter_2_mandatory_count=None,chapter_2_accepted=False,
    selected_historical_migration_paths=2,remaining_main_manifest_missing_paths=21,
    historical_other24_semantic_migration_required=True,future_chapters='3-16 unenumerated and mandatory; null counts are not zero obligations',
    whole_book_goal='active',main_updated=False,live_updated=False))
write('memory-digest-accepted-v2.md','OGD source repair accepted locally only. v1 source coverage rejected, v2 arbitrary-open/source-to-feasible producer closes actual12 bodies/two predicates, both same projected-step inequalities, sharp fixed/unbounded-domain and bounded variable eta(T-1) negative terminals, tuned positive DGT on one same run. Old16 native headers/all fixed/variable code tokens unchanged, stronger RegularLoss explicitly qualified in comments and preserved raw snapshots. Actual30 canaries incl nonconvex supplied U/unbounded axis/nonzero exp gradient/positive regret/terminal1, active projection/T0/T1 zero diameter/strict future-prefix; no formal all-alternative-U nonexistence or every-tuned-step clipping claim.75 unique standard-or-none axiom records,12 actual public safe fences,root9087/Tests9228/full466/7,38 compiled scope nodes/33 proof-value pairs,14 unique new shared registry nodes/10790 old IDsURLs retained,clean site02 and distinct final reader/immutable audit passed. Preserve all actual failures/N/A versus true commit-based contributor gates; exactbase7production/one manifest passed, main21missing remain. Raw logs/four immutable failed/type/snapshot blank-EOF evidence are explicit whitespace exceptions; all other paths checked. Historical inventory preserved via accepted overlay. Draft PR pending; fullChapter2 enumeration/remaining historical migration and Chapters3-16 mandatory. Whole Goal ACTIVE/globalSGB unchanged; no main/live/merge/deploy/human/externalreview claim.')
write('retrieval-index-accepted-v2.md','Reusable same Domain/project/step/iterate/iterateVariable, mathlib Hilbert projection producer/variational characterization, feasible convex_gradient_lower_bound, continuous Riesz linear regularity/gradient, old true affine-instance quadratic lemma and weighted_potential_sum. SourceRegularLoss -> FeasibleRegularLoss adapter supplies actual source semantics. Public frozen12/old16 headers and immutable source/body/final reader hashes:accepted-binding-audit-v2.json. Actual proof-term edges differ from four-note teaching navigation. Source mappings:source-inventory-acceptance-overlay-v2.json, same canonical registry:registry-final02.json. Next close fullChapter2 numbered/unnumbered inventory and remaining historical production migration without changing original contracts or treating manifest coverage as semantic acceptance.')
gate('accepted-reviewer-trial-v2',sys.executable,'-X','utf8','tools/bandit.py','trial-log','--task',task,'--run-id',run.name,
    '--role','reviewer','--kind','review','--status','compiled','--attempt-id','ONLINE-OGD-SOURCE12-BODY-V2',
    '--reviewer-validated','--progress-class','closed-frontier','--verifier-evidence',str(run/'accepted-decision-v2.json'),
    '--notes','Distinct final source reader and immutable audit accept OGD package only;12proofs/30canaries/75axioms/rootTests/full466/7/38graph/33valuepairs/14registry/clean site02/exact7paths. Chapter2/book incomplete; stacked PR pending.')
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
with (run/'accepted-scoped-trials-v2.jsonl').open('w',encoding='utf-8',newline='\n') as f:
    for t in trials:
        if t.get('task')==task:f.write(json.dumps(t)+'\n')
leaf=load('candidate-frontier-v2.json')['current_leaf']
gate('accepted-frontier-refresh-v2',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh',
    '--root-objective','Persistent Orabona Chapters1-16 Goal; OGD source package accepted only, Chapter2/book incomplete',
    '--leaf',task,'--kind','lean','--statement',leaf['statement'],'--declaration',leaf['declaration'],'--file',leaf['file'],
    '--source-status','accepted','--leaf-status','accepted','--dependency','lean:BanditRL.OnlineGradientDescentSource.lemma_2_12:compiled',
    '--dependency','lean:BanditRL.OnlineGradientDescentSource.source_to_feasible:compiled',
    '--dependency','review:final-reader:accepted','--dependency','harness:full-bandit:passed',
    '--trials',str(run/'accepted-scoped-trials-v2.jsonl'),'--output',str(run/'accepted-frontier-v2.json'),'--shadow-status','pending')
gate('accepted-frontier-shadow-v2',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow',
    '--trials',str(run/'accepted-scoped-trials-v2.jsonl'),'--memory-digest',str(run/'memory-digest-accepted-v2.md'),
    '--frontier',str(run/'accepted-frontier-v2.json'))
gate('accepted-lifecycle-v2',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','accepted',
    '--payload-json',json.dumps(dict(run_id=run.name,contract_version=2,scope='OGD source package only',public_proofs=12,
        canaries=30,axioms=75,semantic_verdict=review['verdict'],immutable_raw_rows=audit['raw_review_rows_verified'],
        chapter_complete=False,book_complete=False,goal_complete=False,merged=False,deployed=False)))
print('OGD package accepted locally only; whole Goal active; stacked draft PR delivery still required.')
