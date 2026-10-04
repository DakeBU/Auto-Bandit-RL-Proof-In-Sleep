"""Verify immutable review bindings, exact frozen targets and actual separate gates."""
from pathlib import Path
import hashlib,json,re,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent
def load(n):return json.loads((run/n).read_text(encoding='utf-8'))
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
count=0
def verify(rows,old_test_overlay=False):
    global count
    for row in rows:
        path=row['path']
        if old_test_overlay and path=='Tests/OnlineOptimalStepCanary.lean':
            delta=load('public-body-inputs-v2.json')['supersession']
            assert row['sha256']==delta['old_sha256']
            assert sha(path)==delta['new_sha256']
            path=delta['preserved_snapshot']
        assert sha(path)==row['sha256'],('raw drift',path)
        count+=1
for name in ['source-contract-receipt-v1.json','public-body-receipt.json',
             'public-body-receipt-v2.json','final-reader-receipt.json']:
    receipt=load(name);assert receipt['verdict']=='accepted-with-explicit-delta',name
    verify(receipt['reviewed_files'],old_test_overlay=name=='public-body-receipt.json')
    assert sha(receipt['report'])==receipt['report_sha256'],name
reader=load('final-reader-inputs.json');assert len(reader['canonical_surfaces'])==14
verify(reader['rows'])
blind=load('blind-receipt-v1.json')
for k in ['input','report']:assert sha(blind[k]['path'])==blind[k]['sha256_raw_bytes']
assert blind['scope']['target_count']==11 and blind['scope']['semantic_slots_per_target']==7
assert blind['scope']['source_provenance_name_map_context_proofs_compile_evidence_verdicts_read_this_pass'] is False
assert blind['actor']['task']=='/root/normal_blind'
freeze=load('draft-freeze.json')
context=Path('docs/contracts/online-optimal-step-v1/context.lean.txt')
assert sha(context)==freeze['context_sha256']
public=Path('BanditRLProof/OnlineOptimalStep.lean');text=public.read_text(encoding='utf-8')
def normalize(s):
    s=re.sub(r'/-.*?-/', '',s,flags=re.S);s=re.sub(r'--[^\n]*','',s)
    return ' '.join(s.split())
original=context.read_text(encoding='utf-8').rsplit('end BanditRL.OnlineOptimalStep',1)[0]
assert normalize(text.split('theorem gap_identity',1)[0])==normalize(original),'definition/context drift'
assert len(freeze['headers'])==11
for name,expected in freeze['headers'].items():
    assert hashlib.sha256(lean_declaration_header(public,name).encode('utf-8')).hexdigest()==expected,name
    fence=load('public-candidate-fences/'+name+'.json')
    contract=json.loads(Path('docs/contracts/online-optimal-step-v1/'+name+'.json').read_text(encoding='utf-8'))
    assert fence['file']=='BanditRLProof/OnlineOptimalStep.lean'
    assert fence['statement_hash']==contract['statement_hash']==expected
    assert fence['source_assumptions']==contract['source_assumptions'],name
for row in load('public-actual-bindings.json'):
    assert row['actual_file_raw_sha256']==sha(public) and row['native_guard_exit']==0,row
test=Path('Tests/OnlineOptimalStepCanary.lean')
for name,expected in load('canary-frozen-headers.json').items():
    assert hashlib.sha256(lean_declaration_header(test,name).encode('utf-8')).hexdigest()==expected,name
assert len(re.findall(r'^theorem ',test.read_text(encoding='utf-8'),re.M))==23
for label in ['public-focused-01','canary-03','canary-focused-02','public-axioms-03',
    'root-01','tests-02','full-harness-01','proof-graph-01','graph-verify-01',
    'contributor-exact-base-02','candidate-frontier-refresh-02','candidate-shadow',
    'site-final02-build','site-final02-check','registry-final02','browser-final02','diff-check-scoped-02']:
    assert load(label+'-exit.json')['exit_code']==0,label
contributor=(run/'contributor-exact-base-02.log').read_text(encoding='utf-8')
assert 'affected production paths: 8' in contributor and 'changed contribution contracts: 1' in contributor
assert 'Contributor contract passed.' in contributor and 'Contributor contract N/A' not in contributor
assert load('diff-check-all-exit.json')['exit_code']!=0
assert load('public-axioms-02-exit.json')['exit_code']!=0
assert load('candidate-frontier-refresh-exit.json')['exit_code']!=0
assert load('site-final01-build-exit.json')['exit_code']!=0
native=load('compiled-dependencies.json')
assert sha(native['full_export_path'])==native['full_export_sha256']
assert len(native['required_proof_value_checks'])==11 and native['scope_nodes']==13
reg=load('registry-final02.json')
assert reg['status']=='passed' and len(reg['checks'])==13 and reg['lean_verified'] is True
assert sha(reg['registry_path'])==reg['registry_sha256']
assert all(c['matched'] and c['unique_canonical_node'] for c in reg['checks'])
site=json.loads(Path('tmp/online-optimal-step-site-final02/site-manifest.json').read_text(encoding='utf-8'))
assert site['source_dirty'] is False and site['lean_verified'] is True
assert site['source_commit']=='38236eeac865d1b14ee5e38eb7059ccd11842a33'
audit=load('public-axiom-audit-v2.json')
assert audit['actual_names']==41 and len(audit['checks'])==41
assert sha(audit['log_path'])==audit['log_sha256']
assert all(set(a['axioms'])<=set(['propext','Classical.choice','Quot.sound']) for a in audit['checks'])
assert sha('../research-online-ogd/tmp/pdfs/orabona-v10.pdf')=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
result=dict(status='passed',raw_review_rows_verified=count,source_public_headers=11,
    definition_context_unchanged=True,original_canary_headers_unchanged=22,actual_canary_theorems=23,
    explicit_prior_Test_supersession_retained=True,clean_blind_version=1,
    same_shared_registry_nodes=13,native_proof_value_checks=11,axiom_names=41,
    final_clean_site_commit=site['source_commit'],actual_contributor_production_paths=8,
    rejected_site01_schema_and_axiom02_race_and_frontier01_interface_retained=True,
    full_git_diff_check_passed=False,scoped_diff_check_passed=True,
    whitespace_exception='ONLY this task raw compiler .log outputs; all other paths checked',
    chapter_complete=False,book_complete=False,merged=False,deployed=False)
with (run/'accepted-binding-audit.json').open('w',encoding='utf-8',newline='\n') as f:
    json.dump(result,f,indent=2);f.write('\n')
print(json.dumps(result))
