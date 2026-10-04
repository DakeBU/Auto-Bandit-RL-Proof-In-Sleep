from pathlib import Path
import hashlib,json,subprocess,sys
run=Path('runs/online-osd-20261004')
inv=json.loads((run/'binding-inventory-v2.json').read_text(encoding='utf-8'))
expected=set(inv['expected']);assert len(expected)==len(inv['expected'])
rawchecks=[];reviewed=set()
required={
 'source-contract-receipt.json':'rejected',
 'source-contract-receipt-v3.json':'accepted-with-explicit-delta',
 'source-contract-receipt-causality-v1.json':'accepted-with-explicit-delta',
 'source-contract-receipt-performance-v1.json':'accepted-with-explicit-delta',
 'single-step-body-receipt.json':'accepted-source-leaf-body',
 'algorithm-performance-body-receipt.json':'accepted-with-explicit-delta',
 'public-body-receipt.json':'accepted-with-explicit-delta',
}
for name,verdict in required.items():
 d=json.loads((run/name).read_text(encoding='utf-8-sig'));assert d['verdict']==verdict,(name,d['verdict'])
assert json.loads((run/'final-reader-receipt.json').read_text(encoding='utf-8-sig'))['verdict']=='rejected','historical final registry rejection must stay visible'
last=json.loads((run/'final-reader-receipt-v2.json').read_text(encoding='utf-8-sig'))
assert last['verdict'] in ['accepted','accepted-with-explicit-delta']
for name in list(required)+['final-reader-receipt-v2.json']:
 d=json.loads((run/name).read_text(encoding='utf-8-sig'))
 for row in d['reviewed_files']:
  p=row['path'];actual=hashlib.sha256(Path(p).read_bytes()).hexdigest()
  assert actual==row['sha256'],('raw review drift',name,p)
  reviewed.add(p);rawchecks.append({'receipt':name,'file':p,'raw_sha256':actual})
 assert hashlib.sha256(Path(d['report']).read_bytes()).hexdigest()==d['report_sha256'],('report drift',name)
for name in ['blind-receipt.json','blind-receipt-v2.json','blind-receipt-v3.json','blind-receipt-causality-v1.json','blind-receipt-performance-v1.json','blind-receipt-performance-v2.json']:
 d=json.loads((run/name).read_text(encoding='utf-8-sig'))
 assert hashlib.sha256(Path(d['input']).read_bytes()).hexdigest()==d['input_sha256_raw'],('blind input drift',name)
 assert hashlib.sha256(Path(d['report']).read_bytes()).hexdigest()==d['report_sha256_raw'],('blind report drift',name)
assert set(inv['required_reviewed_production'])<=reviewed,('production review omitted',set(inv['required_reviewed_production'])-reviewed)
normalize=lambda raw:raw.decode('utf-8-sig').replace('\r\n','\n').encode('utf-8')
if '--capture' in sys.argv:
 assert not (run/'roundtrip-bindings-v2.json').exists(),'never silently refresh captured bindings'
 data={'normalization':'UTF8 BOM removal and CRLF to LF only; exact raw receipts independently checked; no JSON reserialization','lf_hashes':{p:hashlib.sha256(normalize(Path(p).read_bytes())).hexdigest() for p in sorted(expected)},'supersessions':[],'historical_rejection_preserved':True}
 with (run/'roundtrip-bindings-v2.json').open('w',encoding='utf-8',newline='\n') as f:json.dump(data,f,indent=2);f.write('\n')
else:
 data=json.loads((run/'roundtrip-bindings-v2.json').read_text());assert set(data['lf_hashes'])==expected;assert data['supersessions']==[]
 for p,h in data['lf_hashes'].items():
  assert hashlib.sha256(normalize(Path(p).read_bytes())).hexdigest()==h,('worktree',p)
  assert hashlib.sha256(normalize(subprocess.check_output(['git','show','HEAD:'+p]))).hexdigest()==h,('HEAD',p)
print(json.dumps({'status':'passed','mode':'capture' if '--capture' in sys.argv else 'worktree-and-HEAD','commit':subprocess.check_output(['git','rev-parse','HEAD']).decode().strip(),'fixed_inventory':len(expected),'raw_receipt_rows':len(rawchecks),'blind_packet_report_pairs':6,'explicit_historical_supersessions':0,'historical_v2_rejection_preserved':True,'historical_final_reader_registry_rejection_preserved':True}))
