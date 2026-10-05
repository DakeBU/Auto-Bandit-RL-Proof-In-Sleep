"""Accept byte-exact current reader review and separately observed gates only."""
from pathlib import Path
import hashlib,json,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
snap={r['path']:r for r in load(run/'historical-raw-supersession-v1.json')['rows']}
count=0;resolved=[]
for name in ['source-contract-receipt-v1.json','public-body-receipt-v1.json','final-reader-receipt-v1.json']:
    r=load(run/name);assert r['verdict']=='accepted-with-explicit-delta'
    assert r['actor']['task']=='/root/source_reviewer'
    assert sha(r['report'])==r['report_sha256'],name
    if name!='public-body-receipt-v1.json':assert not r['required_repairs'],name
    else:assert not r['mathematical_repairs']
    for row in r['reviewed_files']:
        actual=sha(row['path']);original=row['sha256']
        if actual!=original:
            assert name!='final-reader-receipt-v1.json',('final raw drift',row['path'])
            s=snap[row['path']];assert original==sha(s['snapshot'])==s['raw_sha256']
            resolved.append(dict(receipt=name,path=row['path'],snapshot=s['snapshot']))
        count+=1
inputs=load(run/'final-reader-inputs-v1.json')
for row in inputs['rows']:assert sha(row['path'])==row['sha256'],('final inputs drift',row['path']);count+=1
blind=load(run/'blind-receipt-v1.json')
for k in ['input','report']:assert sha(blind[k]['path'])==blind[k]['sha256_raw_bytes']
assert blind['scope']['target_count']==7 and blind['scope']['semantic_slots_per_target']==7
assert blind['scope']['source_maps_proofs_logs_judgments_other_files_read_this_pass'] is False
freeze=load(run/'draft-freeze-v1.json');public=Path('BanditRLProof/OnlineFTLFailure.lean')
assert len(freeze['headers'])==7
for n,h in freeze['headers'].items():
    assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h,n
    assert load(run/('safe-public-v1-'+n+'-exit.json'))['exit_code']==0,n
normalize=lambda s:' '.join(_strip_lean_comments(s).split())
assert normalize(public.read_text(encoding='utf-8'))==normalize((run/'original-public-module.lean.txt').read_text(encoding='utf-8'))
assert sha('Tests/OnlineFTLFailureCanary.lean')==freeze['original_public_canary_sha256']
binding=load(run/'public-actual-bindings-v1.json')
assert len(binding['actual_named_lookup_and_axioms'])==12
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in binding['actual_named_lookup_and_axioms'].values())
gates=['root-v1-01','Tests-v1-01','full-harness-v1-02','contributor-exact-v1-01',
    'site-final01-build','site-final01-check','registry-final01','browser-final01','review-history-v1-02',
    'scoped-diff-v1-02','candidate-frontier-refresh-v1','candidate-frontier-shadow-v1']
for n in gates:assert load(run/(n+'-exit.json'))['exit_code']==0,n
full=(run/'full-harness-v1-02.log').read_text(encoding='utf-8')
assert 'Ran 466 tests' in full and 'OK (skipped=7)' in full and 'check passed' in full
assert load(run/'full-harness-v1-01-exit.json')['exit_code']!=0
exact=(run/'contributor-exact-v1-01.log').read_text(encoding='utf-8')
assert 'affected production paths: 4' in exact and 'changed contribution contracts: 1' in exact
assert 'Contributor contract passed.' in exact and 'N/A' not in exact
graph=load(run/'compiled-dependencies-v1.json')
assert graph['scope_nodes']==10 and len(graph['required_actual_value_pairs'])==6
assert sha(graph['graph_path'])==graph['graph_sha256']
assert graph['new_export'] is False and graph['all_current_Lean_code_tokens_unchanged'] is True
registry=load(run/'registry-final01.json');assert registry['status']=='passed' and len(registry['checks'])==10
assert sha(registry['registry_path'])==registry['registry_sha256']
site=load('tmp/online-ftl-migration-site-final01/site-manifest.json')
assert site['source_dirty'] is False and site['lean_verified'] is True
assert site['source_commit']==inputs['site_commit']==registry['source_commit']
assert load(run/'scoped-diff-v2.json')['status']=='passed'
assert load(run/'full-diff-v1-01-exit.json')['exit_code']!=0
assert sha('../research-online-ogd/tmp/pdfs/orabona-v10.pdf')==freeze['source_pdf_sha256']
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
result=dict(status='passed',raw_review_rows_verified=count,authorized_historical_snapshot_resolutions=resolved,
    retained_public_proofs=7,definitions=3,canary_proofs=2,new_proofs=0,all_code_tokens_unchanged=True,
    actual_axiom_names=12,native_safe_guards=7,actual_reused_graph_scope_nodes=10,required_proof_value_pairs=6,new_export=False,
    shared_registry_scope_nodes=10,new_registry_nodes=0,preserved_old_registry_nodes=registry['preserved_base_node_ids_and_urls'],
    final_clean_site_commit=site['source_commit'],root_jobs=9087,Tests_jobs=9228,full_tests=466,existing_skips=7,
    contributor_production_paths=4,full_git_diff_check_passed=False,scoped_diff_check_passed=True,
    whitespace_exception=load(run/'scoped-diff-v2.json')['reason'],
    chapter_complete=False,book_complete=False,goal_complete=False,merged=False,deployed=False)
with (run/'accepted-binding-audit-v1.json').open('w',encoding='utf-8',newline='\n') as f:json.dump(result,f,indent=2);f.write('\n')
print('Final byte-exact FTL/source/reader package gates passed:',count,'raw rows; retained7 proofs, no chapter/Goal completion.')
