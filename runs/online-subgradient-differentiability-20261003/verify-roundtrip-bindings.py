from pathlib import Path
import re,json,hashlib,subprocess,sys

run=Path('runs/online-subgradient-differentiability-20261003')
prefix=run.as_posix()+'/'
expected={
 'BanditRLProof/OnlineSubgradientDifferentiability.lean','BanditRLProof/OnlineConvexMinorant.lean',
 'BanditRLProof/OnlineSubgradientInterior.lean','BanditRLProof/OnlineSubgradientBasic.lean',
 'BanditRLProof/OnlineConvexExtended.lean','BanditRLProof/OnlineClosedProper.lean',
 'BanditRLProof/OnlineConvexFirstOrder.lean','BanditRLProof.lean','Tests.lean',
 'Tests/OnlineSubgradientDifferentiabilityCanary.lean',
 'website/content/books.json','website/content/chapters.json','website/content/readings.json',
 'website/content/highlights.json','docs/contracts/online-book-v1/source-inventory.json',
 'docs/contracts/online-subgradient-differentiability-v2/contract.md',
 prefix+'blind-packet-v2.txt',prefix+'blind-reconstruction-v2.md',
 prefix+'full-source-review.md',prefix+'public-reader-review.md',
 prefix+'public-reader-repair-review.md',prefix+'acceptance-metadata-review.md',prefix+'raw-review-check.json',
 prefix+'full-candidate.lean.txt',prefix+'full-theorem02.log',
 prefix+'reverse-gradient03.log',prefix+'public-canary01.log'}
superseded={('public-reader-review.md','website/content/readings.json'),
 ('public-reader-review.md','website/content/highlights.json'),
 ('public-reader-review.md','docs/contracts/online-book-v1/source-inventory.json')}
rawchecks=[]
for name in ['full-source-review.md','public-reader-review.md','public-reader-repair-review.md','acceptance-metadata-review.md']:
 text=(run/name).read_text(encoding='utf-8')
 rows=re.findall(r'\| `([^`]+)` \| `([0-9a-f]+)` \|',text)
 assert rows,name
 for p,h in rows:
  actual=hashlib.sha256(Path(p).read_bytes()).hexdigest()
  old=(name,p) in superseded
  if old:
   assert h!=actual,(name,p,'expected preserved historical mismatch')
  else:assert h==actual,(name,p,h,actual)
  rawchecks.append({'receipt':name,'file':p,'raw_sha256':actual,'historical_row_superseded':old})
repair=(run/'public-reader-repair-review.md').read_text(encoding='utf-8')+(run/'acceptance-metadata-review.md').read_text(encoding='utf-8')
for _,p in superseded:
 assert re.search(r'\| `'+re.escape(p)+r'` \| `'+hashlib.sha256(Path(p).read_bytes()).hexdigest()+r'` \|',repair)
assert Path('tmp/online-subgradient-full.lean').read_bytes()==(run/'full-candidate.lean.txt').read_bytes()
normalize=lambda raw:raw.decode('utf-8-sig').replace('\r\n','\n').encode('utf-8')
if '--capture' in sys.argv:
 data={'normalization':'UTF8 without BOM; CRLF to LF only; raw review receipts separately checked',
  'lf_hashes':{p:hashlib.sha256(normalize(Path(p).read_bytes())).hexdigest() for p in sorted(expected)},
  'supersessions':{'public-reader-review.md':['website/content/readings.json','website/content/highlights.json','docs/contracts/online-book-v1/source-inventory.json']}}
 (run/'roundtrip-bindings.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
else:
 data=json.loads((run/'roundtrip-bindings.json').read_text(encoding='utf-8'))
 assert set(data['lf_hashes'])==expected
 for p,h in data['lf_hashes'].items():
  assert hashlib.sha256(normalize(Path(p).read_bytes())).hexdigest()==h,p
  committed=subprocess.check_output(['git','show','HEAD:'+p])
  assert hashlib.sha256(normalize(committed)).hexdigest()==h,('HEAD',p)
print(json.dumps({'status':'passed','mode':'capture' if '--capture' in sys.argv else 'worktree-and-HEAD',
 'commit':subprocess.check_output(['git','rev-parse','HEAD']).decode().strip(),
 'fixed_inventory':len(expected),'raw_receipt_rows':len(rawchecks),
 'explicit_historical_supersessions':len(superseded)}))
