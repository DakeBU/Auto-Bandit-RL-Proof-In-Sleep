from pathlib import Path
import hashlib,json,subprocess,sys
run=Path('runs/online-subgradient-max-20261003');prefix=run.as_posix()+'/'
expected={
 'BanditRLProof/OnlineSubgradientMax.lean','Tests/OnlineSubgradientMaxCanary.lean','BanditRLProof.lean','Tests.lean',
 'BanditRLProof/OnlineSubgradientBasic.lean','BanditRLProof/OnlineSubgradientDifferentiability.lean','BanditRLProof/OnlineSubgradientInterior.lean','BanditRLProof/OnlineConvexExtended.lean','BanditRLProof/OnlineClosedProper.lean',
 'lean-toolchain','lakefile.lean','lake-manifest.json',
 'website/content/books.json','website/content/chapters.json','website/content/readings.json','website/content/highlights.json',
 'docs/contracts/online-book-v1/source-inventory.json','docs/contracts/online-book-v1/coverage.json',
 'research-wiki/contribution-contracts/ONLINE-SUBGRADIENT-MAX-20261003.json',
 'docs/contracts/online-subgradient-max-v1/context.txt','docs/contracts/online-subgradient-max-v1/contract.md','docs/contracts/online-subgradient-max-v1/contract-manifest.json',
 'docs/contracts/online-subgradient-max-v1/active_subgradient_support_max-header.txt','docs/contracts/online-subgradient-max-v1/active_subgradient_support_max.json',
 'docs/contracts/online-subgradient-max-v1/theorem_2_26-header.txt','docs/contracts/online-subgradient-max-v1/theorem_2_26.json',
 prefix+'blind-packet.txt',prefix+'blind-reconstruction.md',prefix+'blind-receipt.json',
 prefix+'source-contract-review.md',prefix+'source-contract-receipt.json',prefix+'source-body-review.md',prefix+'source-body-receipt.json',prefix+'final-reader-review.md',prefix+'final-reader-receipt.json',
 prefix+'attempts/max-full-leaf-01.lean',prefix+'attempts/max-full-leaf-01.log',prefix+'attempts/max-canary-06.lean',prefix+'attempts/max-canary-06.log',
 prefix+'focused-build.log',prefix+'root-build.log',prefix+'tests-build.log',prefix+'full-harness-02.log',prefix+'public-axioms.log',prefix+'axiom-audit.json',prefix+'public-frozen-check.json',
 prefix+'compiled-dependencies.json',prefix+'graph-check.log',prefix+'registry.json',prefix+'site-build-05.log',prefix+'site-check-05.log',prefix+'contributor-gate-02.log',prefix+'visual-review.md',prefix+'global-frontier-preservation.json'
}
rawchecks=[];reviewed=set()
for name in ['source-contract-receipt.json','source-body-receipt.json','final-reader-receipt.json']:
 d=json.loads((run/name).read_text(encoding='utf-8-sig'));assert d['verdict'] in ['accepted','accepted-with-explicit-delta']
 for row in d['reviewed_files']:
  p=row['path'];actual=hashlib.sha256(Path(p).read_bytes()).hexdigest();assert actual==row['sha256'],('raw review drift',name,p)
  reviewed.add(p);rawchecks.append({'receipt':name,'file':p,'raw_sha256':actual})
 assert hashlib.sha256(Path(d['report']).read_bytes()).hexdigest()==d['report_sha256'],('report drift',name)
required_production={
 'BanditRLProof/OnlineSubgradientMax.lean','Tests/OnlineSubgradientMaxCanary.lean','BanditRLProof.lean','Tests.lean',
 'website/content/books.json','website/content/chapters.json','website/content/readings.json','website/content/highlights.json',
 'docs/contracts/online-book-v1/source-inventory.json','docs/contracts/online-book-v1/coverage.json',
 'research-wiki/contribution-contracts/ONLINE-SUBGRADIENT-MAX-20261003.json'
}
assert required_production<=reviewed,('production review omitted',required_production-reviewed)
normalize=lambda raw:raw.decode('utf-8-sig').replace('\r\n','\n').encode('utf-8')
if '--capture' in sys.argv:
 data={'normalization':'UTF8 BOM removal and CRLF to LF only; raw receipt rows independently checked, no JSON reserialization','lf_hashes':{p:hashlib.sha256(normalize(Path(p).read_bytes())).hexdigest() for p in sorted(expected)},'supersessions':[]}
 with (run/'roundtrip-bindings.json').open('w',encoding='utf-8',newline='\n') as z:json.dump(data,z,indent=2);z.write('\n')
else:
 data=json.loads((run/'roundtrip-bindings.json').read_text());assert set(data['lf_hashes'])==expected;assert data['supersessions']==[]
 for p,h in data['lf_hashes'].items():
  assert hashlib.sha256(normalize(Path(p).read_bytes())).hexdigest()==h,('worktree',p)
  assert hashlib.sha256(normalize(subprocess.check_output(['git','show','HEAD:'+p]))).hexdigest()==h,('HEAD',p)
print(json.dumps({'status':'passed','mode':'capture' if '--capture' in sys.argv else 'worktree-and-HEAD','commit':subprocess.check_output(['git','rev-parse','HEAD']).decode().strip(),'fixed_inventory':len(expected),'raw_receipt_rows':len(rawchecks),'explicit_historical_supersessions':0}))
