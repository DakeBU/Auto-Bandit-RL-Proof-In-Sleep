from pathlib import Path
import hashlib,json,subprocess,sys
run=Path('runs/online-guessing-osd-20261004')
inv=json.loads((run/'binding-inventory.json').read_text(encoding='utf-8'))
expected=set(inv['expected']);assert len(expected)==len(inv['expected'])
rawchecks=[];reviewed=set()
required=['source-contract-receipt-v1.json','source-contract-receipt-v2.json','public-body-receipt.json','final-reader-receipt.json']
for name in required:
 d=json.loads((run/name).read_text(encoding='utf-8-sig'));assert d['verdict'] in ['accepted','accepted-with-explicit-delta'],(name,d['verdict'])
 for row in d['reviewed_files']:
  p=row['path'];actual=hashlib.sha256(Path(p).read_bytes()).hexdigest()
  assert actual==row['sha256'],('raw review drift',name,p)
  reviewed.add(p);rawchecks.append({'receipt':name,'file':p,'raw_sha256':actual})
 assert hashlib.sha256(Path(d['report']).read_bytes()).hexdigest()==d['report_sha256'],('report drift',name)
d=json.loads((run/'blind-receipt-v1.json').read_text(encoding='utf-8-sig'))
assert hashlib.sha256(Path(d['input']).read_bytes()).hexdigest()==d['input_sha256_raw']
assert hashlib.sha256(Path(d['report']).read_bytes()).hexdigest()==d['report_sha256_raw']
assert not d['source_inspected'] and not d['proof_inspected'] and not d['source_identity_seen']
assert set(inv['required_reviewed_production'])<=reviewed,('actual canonical read omitted',set(inv['required_reviewed_production'])-reviewed)
# Reject historical failed guard/body/build attempts; never promote draft-path checks.
for name in ['support-fence-01-exit.json','support-fence-02-exit.json','guessing-performance-01-exit.json','public-focused-01-exit.json','canary-focused-01-exit.json']:
 assert json.loads((run/name).read_text(encoding='utf-8'))['exit_code']!=0,(name,'failed history altered')
for row in json.loads((run/'actual-public-candidate-bindings.json').read_text(encoding='utf-8'))['actual_checks']:
 assert row['exit_code']==0 and row['file']=='BanditRLProof/OnlineGuessingSubgradient.lean'
normalize=lambda raw:raw.decode('utf-8-sig').replace('\r\n','\n').encode('utf-8')
if '--capture' in sys.argv:
 assert not (run/'roundtrip-bindings.json').exists(),'never silently refresh captured bindings'
 data={'normalization':'UTF8 BOM removal and CRLF to LF only; raw receipts separately checked; no JSON reserialization','lf_hashes':{p:hashlib.sha256(normalize(Path(p).read_bytes())).hexdigest() for p in sorted(expected)},'supersessions':[],'failed_history_preserved':True}
 with (run/'roundtrip-bindings.json').open('w',encoding='utf-8',newline='\n') as f:json.dump(data,f,indent=2);f.write('\n')
else:
 data=json.loads((run/'roundtrip-bindings.json').read_text());assert set(data['lf_hashes'])==expected;assert data['supersessions']==[]
 for p,h in data['lf_hashes'].items():
  assert hashlib.sha256(normalize(Path(p).read_bytes())).hexdigest()==h,('worktree',p)
  assert hashlib.sha256(normalize(subprocess.check_output(['git','show','HEAD:'+p]))).hexdigest()==h,('HEAD',p)
print(json.dumps({'status':'passed','mode':'capture' if '--capture' in sys.argv else 'worktree-and-HEAD','commit':subprocess.check_output(['git','rev-parse','HEAD']).decode().strip(),'fixed_inventory':len(expected),'raw_receipt_rows':len(rawchecks),'blind_packet_report_pairs':1,'supersessions':0,'failed_guard_and_proof_history_preserved':True,'actual_public_file_fences_required':True}))
