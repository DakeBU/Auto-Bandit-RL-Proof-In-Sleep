"""Recheck immutable raw receipts, exact frozen goals and actual gate results."""
from pathlib import Path
import hashlib,json,re,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent
def load(n):return json.loads((run/n).read_text(encoding='utf-8'))
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for part in iter(lambda:f.read(1048576),b''):h.update(part)
 return h.hexdigest()
count=0
def verify(rows):
 global count
 for row in rows:
  assert sha(row['path'])==row['sha256'],('raw drift',row['path']);count+=1
for name in ['source-contract-receipt-v3.json','public-body-receipt.json','final-reader-receipt-v2.json']:
 d=load(name);assert d['verdict']=='accepted-with-explicit-delta',name
 verify(d['reviewed_files']);assert sha(d['report'])==d['report_sha256'],name
reader=load('final-reader-inputs-v2.json');assert len(reader['canonical_surfaces'])==14
verify(reader['rows'])
blind=load('blind-receipt-v3.json')
for key in ['input','report']:assert sha(blind[key]['path'])==blind[key]['sha256_raw_bytes']
assert blind['scope']['target_count']==18 and blind['scope']['semantic_slots_per_target']==7
assert blind['scope']['other_source_context_proof_or_verdict_files_read'] is False
assert blind['actor']['task']=='/root/normal_blind'
freeze=load('draft-freeze.json');context=Path('docs/contracts/online-linearization-v1/context.lean.txt')
assert sha(context)==freeze['context_sha256']
public=Path('BanditRLProof/OnlineLinearization.lean');text=public.read_text(encoding='utf-8')
def normalize(s):
 s=re.sub(r'/-.*?-/', '',s,flags=re.S);s=re.sub(r'--[^\n]*','',s)
 return ' '.join(s.split())
original=context.read_text(encoding='utf-8').rsplit('end BanditRL.OnlineLinearization',1)[0]
assert normalize(text.split('theorem outputHistory_last',1)[0])==normalize(original),'context drift'
assert len(freeze['headers'])==18
for name,expected in freeze['headers'].items():
 assert hashlib.sha256(lean_declaration_header(public,name).encode('utf-8')).hexdigest()==expected,name
 fence=load('public-candidate-fences/'+name+'.json')
 source=json.loads(Path('docs/contracts/online-linearization-v1/'+name+'.json').read_text(encoding='utf-8'))
 assert fence['file']==str(public).replace('\\','/')
 assert fence['statement_hash']==source['statement_hash']==expected
 assert fence['source_assumptions']==source['source_assumptions'],name
for row in load('public-actual-bindings.json'):
 assert row['actual_file_raw_sha256']==sha(public) and row['native_guard_exit']==0,row
for label in ['public-focused-01','canary-focused-01','root-01','tests-01','public-axioms-01',
 'full-harness-01','full-harness-02','contributor-exact-base-03','proof-graph-01','graph-verify-01',
 'candidate-shadow','site-final05-build','site-final05-check-02','registry-final05',
 'search-schema3-audit','search-js-syntax-01','diff-check-scoped-02']:
 assert load(label+'-exit.json')['exit_code']==0,label
gate_log=(run/'contributor-exact-base-03.log').read_text(encoding='utf-8')
assert 'affected production paths: 9' in gate_log and 'changed contribution contracts: 1' in gate_log
assert 'Contributor contract passed.' in gate_log and 'Contributor contract N/A' not in gate_log
assert load('diff-check-all-exit.json')['exit_code']!=0
assert load('site-final05-check-exit.json')['exit_code']!=0
native=load('compiled-dependencies.json');assert sha(native['full_export_path'])==native['full_export_sha256']
assert len(native['required_proof_value_checks'])==19 and native['scope_nodes']==30
reg=load('registry-final05.json');assert reg['status']=='passed' and len(reg['checks'])==30
assert sha(reg['registry_path'])==reg['registry_sha256'] and reg['lean_verified'] is True
assert all(c['matched'] and c['unique_canonical_node'] for c in reg['checks'])
site=Path('tmp/online-linearization-site-final05/site-manifest.json')
m=json.loads(site.read_text(encoding='utf-8'));assert m['source_dirty'] is False and m['lean_verified'] is True
assert m['source_commit']=='5e96d0c08dfe5631bc9a5e6a92cc4bda71120f53'
axioms=load('public-axiom-audit.json');assert axioms['actual_names']==65 and len(axioms['checks'])==65
assert all(set(a['axioms'])<=set(['propext','Classical.choice','Quot.sound']) for a in axioms['checks'])
assert sha('runs/active_frontier.json')=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
result={'status':'passed','raw_review_rows_verified':count,'source_public_headers':18,
 'definition_context_unchanged':True,'clean_blind_version':3,'clean_blind_pairs':1,
 'same_shared_registry_nodes':30,'native_proof_value_checks':19,'axiom_names':65,
 'final_clean_site_commit':m['source_commit'],'rejected_final04_attribution_retained':True,
 'rejected_reader_v1_contributor_na_retained':True,'actual_contributor_production_paths':9,
 'full_git_diff_check_passed':False,'scoped_diff_check_passed':True,
 'whitespace_exception':'raw task logs and EXACT types-v1/neutral-types-v2/neutral-types-v3 unproved frozen probes; see diff-check-boundary.md',
 'chapter_complete':False,'book_complete':False,'merged':False,'deployed':False}
with (run/'accepted-binding-audit.json').open('w',encoding='utf-8',newline='\n') as f:
 json.dump(result,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps(result))
