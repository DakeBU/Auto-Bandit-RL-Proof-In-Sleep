from pathlib import Path
import json,hashlib,subprocess
r=Path('runs/online-subgradient-interior-20261003')
d=json.loads((r/'roundtrip-bindings.json').read_text(encoding='utf-8'))
expected={'runs/online-subgradient-interior-20261003/blind-packet.txt', 'BanditRLProof/OnlineClosedProper.lean', 'BanditRLProof/OnlineSubgradientBasic.lean', 'runs/online-subgradient-interior-20261003/independent-source-review.md', 'website/content/readings.json', 'runs/online-subgradient-interior-20261003/blind-reconstruction.md', 'website/content/highlights.json', 'Tests/OnlineSubgradientInteriorCanary.lean', 'BanditRLProof/OnlineConvexExtended.lean', 'BanditRLProof/OnlineSubgradientInterior.lean', 'BanditRLProof/OnlineConvexMinorant.lean'}
assert set(d['lf_hashes'])==expected
for f,h in d['lf_hashes'].items():
 assert hashlib.sha256(Path(f).read_text(encoding='utf-8-sig').encode()).hexdigest()==h,f
 raw=subprocess.check_output(['git','show','HEAD:'+f]).decode('utf-8-sig').replace('\r\n','\n')
 assert hashlib.sha256(raw.encode()).hexdigest()==h,f
print(json.dumps({'status':'passed','commit':subprocess.check_output(['git','rev-parse','HEAD']).decode().strip(),'inventory':len(expected)}))
