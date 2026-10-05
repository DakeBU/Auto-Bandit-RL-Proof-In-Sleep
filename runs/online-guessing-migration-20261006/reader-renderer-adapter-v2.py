"""Use the actual proof_bridge renderer field; mathematical reader content unchanged."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent;p=Path('website/content/readings.json')
sha=lambda q:hashlib.sha256(Path(q).read_bytes()).hexdigest()
raw=p.read_bytes();data=json.loads(raw);r=next(x for x in data['readings'] if x['slug']=='online-guessing-ogd')
assert 'proof' in r and 'proof_bridge' not in r
assert len(r['proof']['steps'])==5 and all(set(['title','detail','math','fallback'])<=set(s) for s in r['proof']['steps'])
renderer=Path('website/scripts/build_site.py').read_text(encoding='utf-8')
assert 'proof_bridge = reading.get("proof_bridge")' in renderer
snap=run/'leaves/reader-before-renderer-adapter-v2.json.txt';assert not snap.exists();snap.write_bytes(raw)
r['proof_bridge']=r.pop('proof')
with p.open('w',encoding='utf-8',newline='\n') as f:json.dump(data,f,ensure_ascii=False,indent=2);f.write('\n')
old=json.loads(raw);assert [x for x in old['readings'] if x['slug']!='online-guessing-ogd']==[x for x in data['readings'] if x['slug']!='online-guessing-ogd']
assert next(x for x in old['readings'] if x['slug']=='online-guessing-ogd')['proof']==r['proof_bridge']
out=run/'reader-renderer-adapter-v2.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:json.dump(dict(status='actual-renderer-field-adapted-before-site-build',before_snapshot=snap.as_posix(),before_sha256=sha(snap),after_sha256=sha(p),renderer_sha256=sha('website/scripts/build_site.py'),delta='proof -> proof_bridge; exact five source-to-Lean proof steps unchanged, actual renderer recognized',all_other_readings_unchanged=True,mathematical_repair=False,Lean_change=False),f,indent=2);f.write('\n')
print('Actual proof_bridge field selected; all five proof steps/math/source scopes unchanged.')
