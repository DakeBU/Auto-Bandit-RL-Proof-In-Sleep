"""Fail-closed raw-byte audit for the accepted candidate, including explicit history."""
from pathlib import Path
import hashlib, json, re, sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header

run=Path(__file__).parent
def sha(path):
    digest=hashlib.sha256()
    with Path(path).open('rb') as f:
        for part in iter(lambda:f.read(1048576),b''):digest.update(part)
    return digest.hexdigest()
def load(name):return json.loads((run/name).read_text(encoding='utf-8'))
row_count=0
def verify(rows, historical=None):
    global row_count
    for row in rows:
        path=row['path'];expected=row['sha256']
        if sha(path)!=expected:
            assert historical and path==historical['path'],('unapproved raw drift',path)
            assert expected==historical['historical_sha256'],row
            assert sha(path)==historical['current_sha256'],path
            assert sha(historical['preserved_snapshot'])==expected,historical
        row_count+=1

overlay=load('public-body-receipt-v2.json')
assert overlay['verdict']=='accepted-with-explicit-delta'
assert len(overlay['superseded_rows'])==1
historical=overlay['superseded_rows'][0]
assert historical['path']=='Tests/OnlineSubgradientPolicyCanary.lean'
for name in ['source-contract-receipt-v3.json','public-body-receipt.json','public-body-receipt-v2.json']:
    receipt=load(name)
    assert receipt['verdict']=='accepted-with-explicit-delta',name
    verify(receipt['reviewed_files'],historical if name=='public-body-receipt.json' else None)
    assert sha(receipt['report'])==receipt['report_sha256'],name

blind=load('blind-receipt-v3.json')
for key in ['input','report']:
    assert sha(blind[key]['path'])==blind[key]['sha256_raw_bytes']
assert blind['scope']['target_count']==21 and blind['scope']['semantic_slots_per_target']==7
assert blind['scope']['target_proofs_read'] is False
assert blind['scope']['upstream_proofs_read'] is False
assert blind['scope']['prior_verdicts_read'] is False
assert blind['actor']['task']=='/root/normal_blind'

freeze=load('draft-freeze.json')
context=Path('docs/contracts/online-osd-policy-v1/context.lean.txt')
assert sha(context)==freeze['context_raw_sha256']
public=Path('BanditRLProof/OnlineSubgradientPolicy.lean')
text=public.read_text(encoding='utf-8')
def normalize(s):
    s=re.sub(r'/-.*?-/', '', s, flags=re.S)
    s=re.sub(r'--[^\n]*', '', s)
    return ' '.join(s.split())
original=context.read_text(encoding='utf-8')
original=original.rsplit('end BanditRL.OnlineSubgradientPolicy',1)[0]
assert normalize(text.split('theorem history_zero',1)[0])==normalize(original), 'definition context drift'
assert len(freeze['targets'])==21
for target in freeze['targets']:
    name=target['name'];header=lean_declaration_header(public,name)
    assert hashlib.sha256(header.encode('utf-8')).hexdigest()==target['native_statement_hash'],name
    fence=load('public-candidate-fences/'+name+'.json')
    source_fence=json.loads(Path('docs/contracts/online-osd-policy-v1/'+name+'.json').read_text(encoding='utf-8'))
    assert fence['file']==str(public).replace('\\','/')
    assert fence['statement_hash']==source_fence['statement_hash']==target['native_statement_hash']
    assert fence['source_assumptions']==source_fence['source_assumptions'],name
for row in load('public-actual-candidate-bindings.json'):
    assert row['actual_file']==str(public).replace('\\','/')
    assert row['actual_file_raw_sha256']==sha(public)
    assert row['native_safe_verify_exit']==0

# The only clean final-reader acceptance is version2 after attribution repair.
reader=load('final-reader-receipt-v2.json')
assert reader['verdict']=='accepted-with-explicit-delta'
verify(reader['reviewed_files'])
assert sha(reader['report'])==reader['report_sha256']
inputs=load('final-reader-inputs-v2.json')
assert len(inputs['canonical_surfaces'])==13
verify(inputs['rows'])
for label in ['public-focused-01','canary-focused-02','root-01','tests-02',
 'public-test-axioms-01','full-harness-03','contributor-exact-base-01',
 'proof-graph-01','graph-verify-01','scoped-frontier-shadow',
 'site-build-04','site-check-04','registry-verify-02']:
    assert load(label+'-exit.json')['exit_code']==0,label
native=load('compiled-dependencies.json')
assert sha(native['full_export_path'])==native['full_export_sha256']
assert len(native['required_proof_value_checks'])==21
assert native['scope_nodes']==30
registry=load('registry-final04.json')
assert registry['status']=='passed' and len(registry['checks'])==30
assert registry['lean_verified'] is True
assert sha(registry['registry_path'])==registry['registry_sha256']
assert all(a['matched'] and a['unique_canonical_node'] for a in registry['checks'])
assert load('public-test-axiom-audit.json')['names']==122
assert load('public-test-axiom-audit.json')['bad']==[]
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
result={'status':'passed','raw_review_rows_verified':row_count,
 'source_public_headers':21,'definition_context_unchanged':True,
 'clean_blind_pairs':1,'clean_blind_version':3,
 'historical_body_test_supersessions':[historical],
 'rejected_reader_version1_is_not_acceptance':True,
 'same_shared_registry_nodes':30,'native_proof_value_checks':21,
 'chapter_complete':False,'book_complete':False,'merged':False,'deployed':False}
with (run/'accepted-binding-audit.json').open('w',encoding='utf-8',newline='\n') as f:
    json.dump(result,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps(result))
