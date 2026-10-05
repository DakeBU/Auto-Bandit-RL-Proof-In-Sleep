"""Recheck frozen statements, immutable reviews and separately captured actual gates."""
from pathlib import Path
import hashlib,json,re,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent
def load(n):return json.loads((run/n).read_text(encoding='utf-8'))
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''):h.update(block)
    return h.hexdigest()
count=0
def verify(rows):
    global count
    for row in rows:
        assert sha(row['path'])==row['sha256'],('raw drift',row['path'])
        count+=1
for n in ['source-contract-receipt-v1.json','public-body-receipt-v1.json','final-reader-receipt.json']:
    receipt=load(n);assert receipt['verdict']=='accepted-with-explicit-delta',n
    verify(receipt['reviewed_files'])
    assert sha(receipt['report'])==receipt['report_sha256'],n
reader=load('final-reader-inputs.json');assert len(reader['canonical_surfaces'])==14
verify(reader['rows'])
blind=load('blind-receipt-v1.json')
for k in ['input','report']:assert sha(blind[k]['path'])==blind[k]['sha256_raw_bytes']
assert blind['scope']['target_count']==22 and blind['scope']['semantic_slots_per_target']==7
assert blind['scope']['source_provenance_name_maps_proofs_type_logs_reviews_other_files_read_this_pass'] is False
assert blind['actor']['task']=='/root/normal_blind'
freeze=load('draft-freeze.json')
context=Path('docs/contracts/online-unit-scaling-v1/context.lean.txt')
assert sha(context)==freeze['context_sha256']
public=Path('BanditRLProof/OnlineUnitScaling.lean');text=public.read_text(encoding='utf-8')
def normalize(s):
    s=re.sub(r'/-.*?-/', '',s,flags=re.S);s=re.sub(r'--[^\n]*','',s)
    return ' '.join(s.split())
original=context.read_text(encoding='utf-8').rsplit('end BanditRL.OnlineUnitScaling',1)[0]
assert normalize(text.split('theorem unit_exponents',1)[0])==normalize(original),'definition/context drift'
assert len(freeze['headers'])==22
for name,expected in freeze['headers'].items():
    assert hashlib.sha256(lean_declaration_header(public,name).encode('utf-8')).hexdigest()==expected,name
    fence=load('public-fences/'+name+'.json')
    contract=json.loads(Path('docs/contracts/online-unit-scaling-v1/'+name+'.json').read_text())
    assert fence['file']==public.as_posix()
    assert fence['statement_hash']==contract['statement_hash']==expected
    assert fence['source_assumptions']==contract['source_assumptions'],name
for row in load('public-actual-bindings.json'):
    assert row['actual_file_raw_sha256']==sha(public) and row['native_guard_exit']==0,row
test=Path('Tests/OnlineUnitScalingCanary.lean');canary=load('canary-freeze-v1.json')
assert sha(test)==canary['raw_sha256'] and canary['actual_proof_count']==30
for name,expected in canary['headers'].items():assert lean_declaration_header(test,name)==expected,name
assert len(re.findall(r'^theorem ',test.read_text(encoding='utf-8'),re.M))==30
gates=['public-focused-01','canary-direct-03','canary-focused-01','public-axioms-01',
       'root-01','Tests-01','full-harness-02','proof-graph-compact-01','graph-verify-01',
       'contributor-exact-base-01','candidate-frontier-refresh','candidate-frontier-shadow',
       'site-final02-build','site-final02-check','registry-final02','browser-final02',
       'candidate-scoped-diffcheck-01']
for gate in gates:assert load(gate+'-exit.json')['exit_code']==0,gate
for failed in ['body-05','canary-direct-01','canary-direct-02','lower-body-native-trial',
               'book-mapping-01','full-harness-01','help-graph','site-final01-build',
               'candidate-full-diffcheck-01']:
    assert load(failed+'-exit.json')['exit_code']!=0,failed
contributor=(run/'contributor-exact-base-01.log').read_text(encoding='utf-8')
assert 'affected production paths: 8' in contributor and 'changed contribution contracts: 1' in contributor
assert 'Contributor contract passed.' in contributor and 'Contributor contract N/A' not in contributor
native=load('compiled-dependencies.json')
assert sha(native['full_export_path'])==native['full_export_sha256']
assert len(native['required_proof_value_checks'])==21 and native['scope_nodes']==26
registry=load('registry-final02.json')
assert registry['status']=='passed' and len(registry['checks'])==26
assert sha(registry['registry_path'])==registry['registry_sha256']
assert all(c['matched'] and c['unique_canonical_node'] for c in registry['checks'])
site=json.loads(Path('tmp/online-unit-scaling-site-final02/site-manifest.json').read_text())
assert site['source_dirty'] is False and site['lean_verified'] is True
assert site['source_commit']=='70c63cac7efa59d2a892b563d8affee4266be610'
axioms=load('axiom-audit-v1.json')
assert axioms['actual_named_count']==62 and len(axioms['rows'])==62
for row in axioms['rows']:
    names={x.strip() for x in row['axioms'].split(',') if x.strip()}
    assert names<=set(['propext','Classical.choice','Quot.sound']),row
assert sha('../research-online-ogd/tmp/pdfs/orabona-v10.pdf')=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
result=dict(status='passed',raw_review_rows_verified=count,source_public_headers=22,
    definition_context_unchanged=True,actual_canary_theorems=30,actual_axiom_names=62,
    same_shared_registry_nodes=26,native_proof_value_checks=21,
    final_clean_site_commit=site['source_commit'],actual_contributor_production_paths=8,
    historical_failures_preserved=True,full_git_diff_check_passed=False,
    scoped_diff_check_passed=True,whitespace_exception='ONLY this task raw .log outputs; every other path checked',
    chapter_complete=False,book_complete=False,goal_complete=False,merged=False,deployed=False)
with (run/'accepted-binding-audit.json').open('w',encoding='utf-8',newline='\n') as f:
    json.dump(result,f,indent=2);f.write('\n')
print(json.dumps(result))
