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
 prefix+'source-contract-review.md',prefix+'source-contract-receipt.json',prefix+'source-body-review.md',prefix+'source-body-receipt.json',prefix+'final-reader-review.md',prefix+'final-reader-receipt.json',prefix+'final-reader-review-v2.md',prefix+'final-reader-receipt-v2.json',prefix+'post-review-drift.json',
 prefix+'attempts/max-full-leaf-01.lean',prefix+'attempts/max-full-leaf-01.log',prefix+'attempts/max-canary-06.lean',prefix+'attempts/max-canary-06.log',
 prefix+'focused-build.log',prefix+'root-build.log',prefix+'tests-build.log',prefix+'full-harness-02.log',prefix+'public-axioms.log',prefix+'axiom-audit.json',prefix+'public-frozen-check.json',
 prefix+'compiled-dependencies.json',prefix+'graph-check.log',prefix+'registry.json',prefix+'site-build-05.log',prefix+'site-check-05.log',prefix+'contributor-gate-02.log',prefix+'visual-review.md',prefix+'global-frontier-preservation.json'
}
rawchecks=[];reviewed=set()
for name in ['source-contract-receipt.json','source-body-receipt.json','final-reader-receipt-v2.json']:
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
# Historical receipt is immutable evidence, including its invalidated row.
historical=json.loads((run/'final-reader-receipt.json').read_text(encoding='utf-8-sig'))
repair=json.loads((run/'post-review-drift.json').read_text())
assert len(repair['drift'])==1
supersessions=[]
for row in historical['reviewed_files']:
 p=row['path'];actual=hashlib.sha256(Path(p).read_bytes()).hexdigest()
 if actual!=row['sha256']:
  matches=[r for r in repair['drift'] if r['path']==p and r['sha256']==row['sha256'] and r['current_sha256']==actual]
  assert len(matches)==1,('unreviewed historical drift',p)
  v2=json.loads((run/'final-reader-receipt-v2.json').read_text(encoding='utf-8-sig'))
  assert any(r['path']==p and r['sha256']==actual for r in v2['reviewed_files'])
  supersessions.append({'historical_receipt':'final-reader-receipt.json','path':p,'old_raw_sha256':row['sha256'],'new_raw_sha256':actual,'repair_receipt':'final-reader-receipt-v2.json','reason':repair['reason']})
assert len(supersessions)==1
assert hashlib.sha256(Path(historical['report']).read_bytes()).hexdigest()==historical['report_sha256']
normalize=lambda raw:raw.decode('utf-8-sig').replace('\r\n','\n').encode('utf-8')
if '--capture' in sys.argv:
 data={'normalization':'UTF8 BOM removal and CRLF to LF only; raw receipt rows independently checked, no JSON reserialization','lf_hashes':{p:hashlib.sha256(normalize(Path(p).read_bytes())).hexdigest() for p in sorted(expected)},'supersessions':supersessions}
 with (run/'roundtrip-bindings.json').open('w',encoding='utf-8',newline='\n') as z:json.dump(data,z,indent=2);z.write('\n')
else:
 data=json.loads((run/'roundtrip-bindings.json').read_text());assert set(data['lf_hashes'])==expected;assert data['supersessions']==supersessions
 for p,h in data['lf_hashes'].items():
  assert hashlib.sha256(normalize(Path(p).read_bytes())).hexdigest()==h,('worktree',p)
  assert hashlib.sha256(normalize(subprocess.check_output(['git','show','HEAD:'+p]))).hexdigest()==h,('HEAD',p)
print(json.dumps({'status':'passed','mode':'capture' if '--capture' in sys.argv else 'worktree-and-HEAD','commit':subprocess.check_output(['git','rev-parse','HEAD']).decode().strip(),'fixed_inventory':len(expected),'raw_receipt_rows':len(rawchecks),'explicit_historical_supersessions':len(supersessions)}))
