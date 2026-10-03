from pathlib import Path
import json,hashlib,subprocess
r=Path('runs/online-subgradient-basic-20261003')
d=json.loads((r/'roundtrip-bindings.json').read_text(encoding='utf-8'))
expected={'BanditRLProof/OnlineSubgradientBasic.lean','BanditRLProof/OnlineClosedProper.lean','BanditRLProof/OnlineConvexExtended.lean','Tests/OnlineSubgradientBasicCanary.lean','website/content/readings.json',str(r/'blind-packet.txt').replace('\\','/'),str(r/'blind-reconstruction.md').replace('\\','/'),str(r/'independent-source-review.md').replace('\\','/')}
assert set(d['lf_hashes'])==expected
for f,h in d['lf_hashes'].items():
 assert hashlib.sha256(Path(f).read_text(encoding='utf-8-sig').encode()).hexdigest()==h, f
 raw=subprocess.check_output(['git','show','HEAD:'+f]).decode('utf-8-sig').replace('\r\n','\n')
 assert hashlib.sha256(raw.encode()).hexdigest()==h, f
print(json.dumps({'status':'passed','commit':subprocess.check_output(['git','rev-parse','HEAD']).decode().strip(),'exact_inventory_count':len(expected),'working_tree_and_commit_lf_hashes_match':True},indent=2))
