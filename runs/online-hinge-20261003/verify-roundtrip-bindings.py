from pathlib import Path
import hashlib,json,subprocess,sys
run=Path('runs/online-hinge-20261003');prefix=run.as_posix()+'/'
expected={
 'BanditRLProof/OnlineHinge.lean','Tests/OnlineHingeCanary.lean','BanditRLProof.lean','Tests.lean',
 'BanditRLProof/OnlineSubgradientMax.lean','BanditRLProof/OnlineSubgradientBasic.lean','BanditRLProof/OnlineConvexExtended.lean','BanditRLProof/OnlineSubgradientDifferentiability.lean',
 'lean-toolchain','lakefile.lean','lake-manifest.json',
 'website/content/books.json','website/content/chapters.json','website/content/readings.json','website/content/highlights.json','website/scripts/build_site.py',
 'docs/contracts/online-book-v1/source-inventory.json','docs/contracts/online-book-v1/coverage.json',
 'research-wiki/contribution-contracts/ONLINE-HINGE-20261003.json',
 'docs/contracts/online-hinge-v1/context.txt','docs/contracts/online-hinge-v1/contract.md','docs/contracts/online-hinge-v1/contract-manifest.json',
 'docs/contracts/online-hinge-v1/affine_subdifferential-header.txt','docs/contracts/online-hinge-v1/affine_subdifferential.json',
 'docs/contracts/online-hinge-v1/example_2_27-header.txt','docs/contracts/online-hinge-v1/example_2_27.json',
 prefix+'blind-packet.txt',prefix+'blind-reconstruction.md',prefix+'blind-receipt.json',
 prefix+'source-contract-review.md',prefix+'source-contract-receipt.json',prefix+'source-body-review.md',prefix+'source-body-receipt.json',
 prefix+'public-body-review.md',prefix+'public-body-review.json',prefix+'public-body-reviewer-trial.json',
 prefix+'final-reader-review.md',prefix+'final-reader-receipt.json',
 prefix+'attempts/hinge-full-02.lean',prefix+'attempts/hinge-full-02.log',prefix+'attempts/hinge-full-02-exit.json',
 prefix+'attempts/hinge-canary-03.lean',prefix+'attempts/hinge-canary-03.log',prefix+'attempts/hinge-canary-03-exit.json',
 prefix+'focused-build.log',prefix+'focused-build-exit.json',prefix+'root-build.log',prefix+'root-build-exit.json',prefix+'tests-build.log',prefix+'tests-build-exit.json',
 prefix+'full-harness-03.log',prefix+'full-harness-03-exit.json',prefix+'public-axioms.log',prefix+'public-axioms-exit.json',prefix+'axiom-audit.json',
 prefix+'public-affine-fence.json',prefix+'public-hinge-fence.json',prefix+'compiled-dependencies.json',prefix+'graph-check.log',prefix+'registry.json',
 prefix+'site-build-04.log',prefix+'site-check-04.log',prefix+'site-build-04-exit.json',prefix+'site-check-04-exit.json',
 prefix+'contributor-gate-02.log',prefix+'contributor-gate-02-exit.json',prefix+'global-frontier-preservation.json',prefix+'scoped-frontier-shadow.json',
 prefix+'visual-review.md',prefix+'visual-receipt.json'
}
rawchecks=[];reviewed=set()
for name in ['source-contract-receipt.json','source-body-receipt.json','public-body-review.json','final-reader-receipt.json']:
 d=json.loads((run/name).read_text(encoding='utf-8-sig'));assert d['verdict'] in ['accepted','accepted-with-explicit-delta']
 for row in d['reviewed_files']:
  p=row['path'];actual=hashlib.sha256(Path(p).read_bytes()).hexdigest();assert actual==row['sha256'],('raw review drift',name,p)
  reviewed.add(p);rawchecks.append({'receipt':name,'file':p,'raw_sha256':actual})
 assert hashlib.sha256(Path(d['report']).read_bytes()).hexdigest()==d['report_sha256'],('report drift',name)
required_production={
 'BanditRLProof/OnlineHinge.lean','Tests/OnlineHingeCanary.lean','BanditRLProof.lean','Tests.lean',
 'website/content/books.json','website/content/chapters.json','website/content/readings.json','website/content/highlights.json','website/scripts/build_site.py',
 'docs/contracts/online-book-v1/source-inventory.json','docs/contracts/online-book-v1/coverage.json',
 'research-wiki/contribution-contracts/ONLINE-HINGE-20261003.json'
}
assert required_production<=reviewed,('production review omitted',required_production-reviewed)
normalize=lambda raw:raw.decode('utf-8-sig').replace('\r\n','\n').encode('utf-8')
if '--capture' in sys.argv:
 data={'normalization':'UTF8 BOM removal and CRLF to LF only; raw receipt rows independently checked, no JSON reserialization','lf_hashes':{p:hashlib.sha256(normalize(Path(p).read_bytes())).hexdigest() for p in sorted(expected)},'supersessions':[]}
 with (run/'roundtrip-bindings.json').open('w',encoding='utf-8',newline='\n') as f:json.dump(data,f,indent=2);f.write('\n')
else:
 data=json.loads((run/'roundtrip-bindings.json').read_text());assert set(data['lf_hashes'])==expected;assert data['supersessions']==[]
 for p,h in data['lf_hashes'].items():
  assert hashlib.sha256(normalize(Path(p).read_bytes())).hexdigest()==h,('worktree',p)
  assert hashlib.sha256(normalize(subprocess.check_output(['git','show','HEAD:'+p]))).hexdigest()==h,('HEAD',p)
print(json.dumps({'status':'passed','mode':'capture' if '--capture' in sys.argv else 'worktree-and-HEAD','commit':subprocess.check_output(['git','rev-parse','HEAD']).decode().strip(),'fixed_inventory':len(expected),'raw_receipt_rows':len(rawchecks),'explicit_historical_supersessions':0}))
