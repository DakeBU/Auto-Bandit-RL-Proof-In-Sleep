from pathlib import Path
import hashlib,json,re,subprocess,sys

run=Path('runs/online-subgradient-sum-20261003');prefix=run.as_posix()+'/'
expected={
 'BanditRLProof/OnlineSubgradientSum.lean','Tests/OnlineSubgradientSumCanary.lean','BanditRLProof.lean','Tests.lean',
 'BanditRLProof/OnlineConvexSums.lean','BanditRLProof/OnlineConvexFirstOrder.lean','BanditRLProof/OnlineConvexBarycenter.lean',
 'BanditRLProof/OnlineClosedProper.lean','BanditRLProof/OnlineSubgradientBasic.lean','BanditRLProof/OnlineConvexExtended.lean',
 'website/content/books.json','website/content/chapters.json','website/content/readings.json','website/content/highlights.json',
 'docs/contracts/online-book-v1/source-inventory.json',
 'research-wiki/contribution-contracts/ONLINE-SUBGRADIENT-SUM-20261003.json',
 'docs/contracts/online-subgradient-sum-v1/context.txt','docs/contracts/online-subgradient-sum-v1/contract.md',
 'docs/contracts/online-subgradient-sum-v1/inclusion-header.txt','docs/contracts/online-subgradient-sum-v1/equality-header.txt',
 'docs/contracts/online-subgradient-sum-v1/contract-manifest.json',
 'docs/contracts/online-subgradient-sum-v1/theorem_2_23_inclusion.json','docs/contracts/online-subgradient-sum-v1/theorem_2_23_equality.json',
 prefix+'blind-packet-v2.txt',prefix+'blind-reconstruction-v2.md',prefix+'full-source-review.md',prefix+'public-reader-review.md',
 prefix+'equality-candidate03.lean.txt',prefix+'equality-canary-candidate02.lean.txt',prefix+'equality-leaf03.log',prefix+'equality-canary02.log',
 prefix+'public-focused02.log',prefix+'full-gate01.log',prefix+'public-axiom-audit01.log',prefix+'axiom-audit.json',
 prefix+'public-frozen-check.json',prefix+'compiled-dependencies.json',prefix+'graph-check01.log',prefix+'site-check02.log',
 prefix+'registry01.json',prefix+'contributor-gate03.log',prefix+'site-build02.log',prefix+'site-check01.log'
}

rawchecks=[];reviewed=set()
for name in ['full-source-review.md','public-reader-review.md']:
    text=(run/name).read_text(encoding='utf-8')
    rows=re.findall(r'\| `([^`]+)` \| `([0-9a-fA-F]{64})` \|',text)
    assert rows,('missing raw review table',name)
    for path,recorded in rows:
        actual=hashlib.sha256(Path(path).read_bytes()).hexdigest()
        assert actual==recorded.lower(),('raw receipt drift',name,path,recorded,actual)
        reviewed.add(path);rawchecks.append({'receipt':name,'file':path,'raw_sha256':actual})
required_production={
 'BanditRLProof/OnlineSubgradientSum.lean','Tests/OnlineSubgradientSumCanary.lean','BanditRLProof.lean','Tests.lean',
 'website/content/books.json','website/content/chapters.json','website/content/readings.json','website/content/highlights.json',
 'docs/contracts/online-book-v1/source-inventory.json','research-wiki/contribution-contracts/ONLINE-SUBGRADIENT-SUM-20261003.json'
}
assert required_production<=reviewed,('review omitted production inventory',required_production-reviewed)
assert Path('tmp/online-subgradient-sum-equality.lean').read_bytes()==(run/'equality-candidate03.lean.txt').read_bytes()
assert Path('tmp/online-subgradient-sum-equality-canary.lean').read_bytes()==(run/'equality-canary-candidate02.lean.txt').read_bytes()
normalize=lambda raw:raw.decode('utf-8-sig').replace('\r\n','\n').encode('utf-8')
if '--capture' in sys.argv:
    data={'normalization':'UTF8 without BOM; CRLF to LF only; raw review receipts independently checked, no JSON reserialization',
          'lf_hashes':{p:hashlib.sha256(normalize(Path(p).read_bytes())).hexdigest() for p in sorted(expected)},'supersessions':[]}
    with (run/'roundtrip-bindings.json').open('w',encoding='utf-8',newline='\n') as out:json.dump(data,out,indent=2);out.write('\n')
else:
    data=json.loads((run/'roundtrip-bindings.json').read_text(encoding='utf-8'))
    assert set(data['lf_hashes'])==expected,('fixed immutable inventory drift',set(data['lf_hashes'])^expected)
    assert data['supersessions']==[]
    for p,h in data['lf_hashes'].items():
        assert hashlib.sha256(normalize(Path(p).read_bytes())).hexdigest()==h,('worktree',p)
        committed=subprocess.check_output(['git','show','HEAD:'+p])
        assert hashlib.sha256(normalize(committed)).hexdigest()==h,('committed HEAD',p)
print(json.dumps({'status':'passed','mode':'capture' if '--capture' in sys.argv else 'worktree-and-HEAD',
 'commit':subprocess.check_output(['git','rev-parse','HEAD']).decode().strip(),
 'fixed_inventory':len(expected),'raw_receipt_rows':len(rawchecks),'explicit_historical_supersessions':0}))
