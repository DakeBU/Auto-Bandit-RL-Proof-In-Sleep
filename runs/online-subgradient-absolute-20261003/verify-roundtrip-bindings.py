from pathlib import Path
import hashlib,json,re,subprocess,sys
run=Path('runs/online-subgradient-absolute-20261003');prefix=run.as_posix()+'/'
expected={
 'BanditRLProof/OnlineSubgradientAbsolute.lean','Tests/OnlineSubgradientAbsoluteCanary.lean','BanditRLProof.lean','Tests.lean',
 'BanditRLProof/OnlineSubgradientBasic.lean',
 'website/content/books.json','website/content/chapters.json','website/content/readings.json','website/content/highlights.json',
 'docs/contracts/online-book-v1/source-inventory.json','research-wiki/contribution-contracts/ONLINE-SUBGRADIENT-ABSOLUTE-20261003.json',
 'docs/contracts/online-subgradient-absolute-v1/context.txt','docs/contracts/online-subgradient-absolute-v1/contract.md','docs/contracts/online-subgradient-absolute-v1/contract-manifest.json',
 'docs/contracts/online-subgradient-absolute-v1/abs_subgradient_positive-header.txt','docs/contracts/online-subgradient-absolute-v1/abs_subgradient_zero-header.txt','docs/contracts/online-subgradient-absolute-v1/abs_subgradient_negative-header.txt','docs/contracts/online-subgradient-absolute-v1/example_2_24-header.txt',
 'docs/contracts/online-subgradient-absolute-v1/abs_subgradient_positive.json','docs/contracts/online-subgradient-absolute-v1/abs_subgradient_zero.json','docs/contracts/online-subgradient-absolute-v1/abs_subgradient_negative.json','docs/contracts/online-subgradient-absolute-v1/example_2_24.json',
 prefix+'blind-packet-v2.txt',prefix+'blind-reconstruction-v2.md',prefix+'draft-source-review.md',prefix+'full-source-review.md',prefix+'public-reader-review.md',
 prefix+'full-candidate02.lean.txt',prefix+'full-canary-candidate02.lean.txt',prefix+'full-leaf02.log',prefix+'full-canary02.log',prefix+'public-focused01.log',
 prefix+'full-gate01.log',prefix+'public-axioms01.log',prefix+'axiom-audit.json',prefix+'public-frozen-check.json',prefix+'compiled-dependencies.json',prefix+'graph-check01.log',
 prefix+'site-build02.log',prefix+'site-check02.log',prefix+'site-build03.log',prefix+'site-check03.log',prefix+'registry01.json',prefix+'registry02.json',prefix+'contributor-gate01.log',prefix+'visual-review.md'
}
rawchecks=[];reviewed=set()
for name in ['draft-source-review.md','full-source-review.md','public-reader-review.md']:
 text=(run/name).read_text(encoding='utf-8');rows=re.findall(r'\| `([^`]+)` \| `([0-9a-fA-F]{64})` \|',text);assert rows,('missing raw receipt table',name)
 for path,h in rows:
  actual=hashlib.sha256(Path(path).read_bytes()).hexdigest();assert actual==h.lower(),('raw receipt drift',name,path,h,actual)
  reviewed.add(path);rawchecks.append({'receipt':name,'file':path,'raw_sha256':actual})
required_production={
 'BanditRLProof/OnlineSubgradientAbsolute.lean','Tests/OnlineSubgradientAbsoluteCanary.lean','BanditRLProof.lean','Tests.lean',
 'website/content/books.json','website/content/chapters.json','website/content/readings.json','website/content/highlights.json',
 'docs/contracts/online-book-v1/source-inventory.json','research-wiki/contribution-contracts/ONLINE-SUBGRADIENT-ABSOLUTE-20261003.json'
}
assert required_production<=reviewed,('production review omitted',required_production-reviewed)
assert Path('tmp/online-subgradient-absolute-full.lean').read_bytes()==(run/'full-candidate02.lean.txt').read_bytes()
assert Path('tmp/online-subgradient-absolute-full-canary.lean').read_bytes()==(run/'full-canary-candidate02.lean.txt').read_bytes()
normalize=lambda raw:raw.decode('utf-8-sig').replace('\r\n','\n').encode('utf-8')
if '--capture' in sys.argv:
 data={'normalization':'UTF8 without BOM; CRLF to LF only; raw review rows independently checked, no JSON reserialization','lf_hashes':{p:hashlib.sha256(normalize(Path(p).read_bytes())).hexdigest() for p in sorted(expected)},'supersessions':[]}
 with (run/'roundtrip-bindings.json').open('w',encoding='utf-8',newline='\n') as f:json.dump(data,f,indent=2);f.write('\n')
else:
 data=json.loads((run/'roundtrip-bindings.json').read_text(encoding='utf-8'));assert set(data['lf_hashes'])==expected;assert data['supersessions']==[]
 for p,h in data['lf_hashes'].items():
  assert hashlib.sha256(normalize(Path(p).read_bytes())).hexdigest()==h,('worktree',p)
  assert hashlib.sha256(normalize(subprocess.check_output(['git','show','HEAD:'+p]))).hexdigest()==h,('HEAD',p)
print(json.dumps({'status':'passed','mode':'capture' if '--capture' in sys.argv else 'worktree-and-HEAD','commit':subprocess.check_output(['git','rev-parse','HEAD']).decode().strip(),'fixed_inventory':len(expected),'raw_receipt_rows':len(rawchecks),'explicit_historical_supersessions':0}))
