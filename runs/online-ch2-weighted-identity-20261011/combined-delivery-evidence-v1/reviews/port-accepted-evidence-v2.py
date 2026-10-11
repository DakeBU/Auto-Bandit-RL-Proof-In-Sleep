"""Create-only evidence port, run only after final bounded package review."""
from pathlib import Path
import datetime,gzip,hashlib,json,subprocess
ROOT=Path.cwd()
SRC=ROOT/'tmp/online-ch2-weighted-final-review-20261011'
DST=ROOT/'runs/online-ch2-weighted-identity-20261011/combined-delivery-evidence-v1'
def sha(b):return hashlib.sha256(b).hexdigest()
def write(p,b):
 p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('xb') as f:f.write(b)
def data(p):return json.loads(p.read_bytes())
def artifact(origin,rel,derived=False):
 raw=origin.read_bytes();out=gzip.compress(raw,mtime=0) if derived else raw
 dest=DST/rel;write(dest,out)
 row={'origin':origin.relative_to(ROOT).as_posix(),'origin_raw_sha256':sha(raw),'destination':dest.relative_to(ROOT).as_posix(),'destination_sha256':sha(out),'bytes':len(out),'mode':'gzip-mtime0-derived' if derived else 'exact-byte-copy'}
 if derived:
  assert gzip.decompress(out)==raw
  row['decompressed_sha256']=sha(gzip.decompress(out))
 rows.append(row)
review=data(SRC/'fresh-final-bounded-package-review-v1.json')
assert review.get('blocking_repairs')==[],review
assert 'accepted' in review.get('verdict',''),review
assert subprocess.check_output(['git','rev-parse','HEAD']).decode().strip()=='c071e678cdd563a847b71e84ae3b4fc1d54faee9'
assert subprocess.check_output(['git','status','--porcelain'])==b''
assert not DST.exists()
packet=data(SRC/'final-candidate-packet-v1.json')
for item in packet['evidence']:
 assert sha((ROOT/item['path']).read_bytes())==item['sha256'],item['path']
rows=[]
attributes=b'* -text\n*.raw -diff\n*.txt -diff\n*.py -diff\n*.cjs -diff\n*.html -diff\n'
write(DST/'.gitattributes',attributes)
gates=ROOT/'tmp/online-ch2-weighted-identity-gates-20261011'
for group in ['combined-v1','site-build-v1','site-check-v1']:
 for p in sorted((gates/'evidence'/group).iterdir()):
  if p.is_file():artifact(p,Path('gates')/group/p.name)
for name in ['contributor-v2.json','contributor-v2-stdout.raw','contributor-v2-stderr.raw','structural-QA-v1.json','structural-QA-v2.json','structural-QA-v3.json','remote-source-v1.json','capture-gate-v1.py','capture-gate-v2.py','capture-gate-v3.py','capture-gate-v4.py','gate-capture-proposal-v1.json','gate-capture-proposal-v2.json']:
 artifact(gates/name,Path('gates')/name)
for p in sorted((gates/'evidence/root-v1').iterdir()):
 if p.is_file():artifact(p,Path('gates/root-precommand-abort-v1')/p.name)
for dirname,rel in [('tmp/online-ch2-weighted-site-qa-plan-20261011','structural'),('tmp/online-ch2-weighted-render-20261011-v1','reader'),('tmp/online-ch2-weighted-final-review-20261011','reviews')]:
 for p in sorted((ROOT/dirname).iterdir()):
  if p.is_file():artifact(p,Path(rel)/p.name)
site=ROOT/'tmp/online-ch2-weighted-identity-site-20261011-v1'
for name in ['site-manifest.json','chapters/online-ogd/index.html','modules/banditrlproof-onlineweightedpotential/index.html']:
 artifact(site/name,Path('site')/name)
artifact(site/'books/registry.json',Path('site/current-registry.json.gz'),True)
artifact(ROOT/'tmp/online-ch2-adaptive-osd-site-20261011-v2/books/registry.json',Path('site/previous-registry.json.gz'),True)
manifest={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'origin':'Actual ignored tmp command/render/review outputs created before this later port','source_commit':'c071e678cdd563a847b71e84ae3b4fc1d54faee9','source_unchanged':True,'rows':rows,'attributes_sha256':sha(attributes),'final_review_sha256':sha((SRC/'fresh-final-bounded-package-review-v1.json').read_bytes()),'scope':'Exact-byte copy except two explicitly derived deterministic gzip registry archives. Fresh browser profiles retained ignored and never inspected/copied as review artifacts. No claim entire site/repository archived or native workflow enforced.'}
write(DST/'port-manifest-v1.json',(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
for row in rows:
 assert sha((ROOT/row['origin']).read_bytes())==row['origin_raw_sha256']
 assert sha((ROOT/row['destination']).read_bytes())==row['destination_sha256']
print(json.dumps({'destination':str(DST),'artifacts':len(rows),'manifest_sha256':sha((DST/'port-manifest-v1.json').read_bytes())},indent=2))
