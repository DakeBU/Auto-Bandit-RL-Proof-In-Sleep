"""Accept only exact reviewed bytes and separately observed actual package gates."""
from pathlib import Path
import hashlib,json,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
count=0;superseded=[]
snap={x['path']:x for x in load(run/'historical-raw-supersession-v2.json')['rows']}
for name,verdict in [('source-contract-receipt-v1.json','rejected'),
    ('source-contract-receipt-v2.json','accepted-with-explicit-delta'),
    ('public-body-receipt-v2.json','accepted-with-explicit-delta'),
    ('final-reader-receipt-v2.json','accepted-with-explicit-delta')]:
    r=load(run/name);assert r['verdict']==verdict
    assert sha(r['report'])==r['report_sha256'],name
    if name!='source-contract-receipt-v1.json':assert not r['required_repairs'],name
    for row in r['reviewed_files']:
        actual=sha(row['path'])
        if actual!=row['sha256']:
            assert name!='final-reader-receipt-v2.json',('final live raw drift',row['path'])
            s=snap[row['path']]
            assert s['raw_sha256']==row['sha256']==sha(s['snapshot'])
            superseded.append(dict(receipt=name,path=row['path'],snapshot=s['snapshot']))
        count+=1
inputs=load(run/'final-reader-inputs-v2.json')
for row in inputs['rows']:assert sha(row['path'])==row['sha256'],('final inputs drift',row['path']);count+=1
for v in [1,2]:
    b=load(run/('blind-receipt-v'+str(v)+'.json'))
    for k in ['input','report']:assert sha(b[k]['path'])==b[k]['sha256_raw_bytes']
    assert b['actor']['task']=='/root/normal_blind' and b['scope']['semantic_slots_per_target']==7
old=load('docs/contracts/online-ogd-migration-v1/native-headers-v1.json');assert len(old)==16
for n,r in old.items():assert hashlib.sha256(lean_declaration_header(Path(r['file']),n).encode()).hexdigest()==r['statement_hash'],n
normalize=lambda s:' '.join(_strip_lean_comments(s).split())
for path in ['BanditRLProof/OnlineGradientDescent.lean','BanditRLProof/OnlineGradientDescentVariable.lean']:
    assert normalize(Path(path).read_text(encoding='utf-8'))==normalize(Path(snap[path]['snapshot']).read_text(encoding='utf-8')),path
freeze=load(run/'freeze-review-v2.json');public=Path('BanditRLProof/OnlineGradientDescentSource.lean')
assert sha('docs/contracts/online-ogd-migration-v2/context.lean.txt')==freeze['context_sha256']
assert sha('docs/contracts/online-ogd-migration-v2/source-intent.md')==freeze['source_intent_sha256']
assert len(freeze['headers'])==12
for n,h in freeze['headers'].items():
    assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h,n
    fence=load(run/('public-fences/'+n+'.json'));assert fence['statement_hash']==h and fence['file']==public.as_posix()
    assert load(run/('safe-public-v2-'+n+'-exit.json'))['exit_code']==0,n
binding=load(run/'public-actual-bindings-v2.json')
assert sha(public)==binding['public_module_sha256'] and sha('Tests/OnlineGradientDescentSourceCanary.lean')==binding['public_canary_sha256']
assert len(binding['actual_named_lookup_and_axioms'])==75
assert all(set(xs)<={'propext','Classical.choice','Quot.sound'} for xs in binding['actual_named_lookup_and_axioms'].values())
gates=['root-v2-02','Tests-v2-02','full-harness-v2-02','contributor-exact-v2-04','graph-verify-v2-01',
    'site-final02-build','site-final02-check','registry-final02','browser-final02','review-history-v2-01',
    'current-diff-v2-02','candidate-frontier-refresh-v2','candidate-frontier-shadow-v2']
for label in gates:assert load(run/(label+'-exit.json'))['exit_code']==0,label
full=(run/'full-harness-v2-02.log').read_text(encoding='utf-8')
assert 'Ran 466 tests' in full and 'OK (skipped=7)' in full and 'check passed' in full
exact=(run/'contributor-exact-v2-04.log').read_text(encoding='utf-8')
assert 'affected production paths: 7' in exact and 'changed contribution contracts: 1' in exact
assert 'Contributor contract passed.' in exact and 'N/A' not in exact
assert load(run/'contributor-exact-v2-02-exit.json')['exit_code']!=0
assert load(run/'diff-check-v2-01-exit.json')['exit_code']!=0
assert load(run/'site-final01-check-exit.json')['exit_code']!=0
assert load(run/'current-scoped-diffcheck-v2.json')['status']=='passed'
graph=load(run/'compiled-dependencies-v2.json')
assert graph['scope_nodes']==38 and len(graph['required_proof_value_checks'])==33
assert sha(graph['full_export_path'])==graph['full_export_sha256']
registry=load(run/'registry-final02.json');assert registry['status']=='passed' and len(registry['checks'])==14
assert registry['preserved_base_node_ids_and_urls']==10790 and sha(registry['registry_path'])==registry['registry_sha256']
site=load('tmp/online-ogd-migration-site-final02/site-manifest.json')
assert site['source_dirty'] is False and site['lean_verified'] is True
assert site['source_commit']==inputs['site_commit']==registry['source_commit']
assert sha('../research-online-ogd/tmp/pdfs/orabona-v10.pdf')=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
result=dict(status='passed',raw_review_rows_verified=count,authorized_historical_snapshot_resolutions=superseded,
    source_public_headers=12,source_public_definitions=2,old16_headers_and_all_code_tokens_unchanged=True,
    actual_canary_theorems=30,actual_axiom_names=75,actual_safe_fences=12,actual_graph_scope_nodes=38,
    native_proof_value_checks=33,new_same_shared_registry_nodes=14,preserved_old_registry_nodes=10790,
    final_clean_site_commit=site['source_commit'],actual_contributor_production_paths=7,
    full_tests=466,existing_skips=7,full_git_diff_check_passed=False,scoped_diff_check_passed=True,
    whitespace_exception='Task raw .logs plus four exact immutable prior draft/type/snapshot blank EOF inputs; all other package paths checked.',
    chapter_complete=False,book_complete=False,goal_complete=False,merged=False,deployed=False)
with (run/'accepted-binding-audit-v2.json').open('w',encoding='utf-8',newline='\n') as f:json.dump(result,f,indent=2);f.write('\n')
print('Exact final source/reader/binding gates passed;',count,'raw rows; Chapter2/book/Goal incomplete.')
