from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;R=P.parent.parent
def bind(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return dict(path=str(p.resolve()),bytes=p.stat().st_size,sha256=h.hexdigest())
header=R/'tmp/online-b4-next-stability-freeze-20261012/neutral-frozen-header-v1.txt';text=header.read_text(encoding='utf-8')
probe=text.replace('theorem cumulative_optimistic_stability {E : Type*}','#check ∀ {E : Type*}').replace('(q : E) (hq : q ∈ V) :','(q : E) (hq : q ∈ V),')
with (P/'HeaderElaboration-v1.lean').open('xb') as f:f.write(probe.encode())
v6=R/'tmp/online-b4-vector-adapter-alpha-comparator-20261012/v6/pins-v6.json';vp=json.loads(v6.read_text());python=Path('C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe')
parents=[R/'BanditRLProof'/n for n in ['OnlineStrongConvexSupport.lean','OnlineStrongConvexMinimum.lean','OnlinePrescientBregmanSource.lean','OnlineClosedProper.lean','OnlineConvexExtended.lean']]
parents += [R/'.lake/build/lib/lean/BanditRLProof'/n for n in ['OnlineStrongConvexSupport.olean','OnlineStrongConvexMinimum.olean','OnlinePrescientBregmanSource.olean','OnlineClosedProper.olean','OnlineConvexExtended.olean']]
parents += [R/'.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Algebra/BigOperators/Group/Finset/Basic.olean']
release=R/'tmp/online-b4-next-stability-freeze-20261012/ignored-core-Lean-resource-release-v1.json';assert bind(release)['sha256']=='d81f37d70561614b888422c9ace2bd2cd3ca2d7371a892d7b053737cfbcb74fa'
pins=dict(python=bind(python),compiler=bind(Path(vp['lean_executable']['path'])),operative_search_pins=bind(v6),ordered_search_roots=vp['allowed_real_search_roots'],release=bind(release),frozen_header=bind(header),header_probe=bind(P/'HeaderElaboration-v1.lean'),parents=[bind(p) for p in parents],project=[bind(R/n) for n in ['lean-toolchain','lakefile.lean','lake-manifest.json','BanditRLProof.lean','Tests.lean']],freeze=bind(R/'tmp/online-b4-next-stability-freeze-20261012/local-header-freeze-v1.json'),capture=bind(P/'capture-v1.py'))
with (P/'capture-pins-v1.json').open('x',encoding='utf-8') as f:json.dump(pins,f,indent=2)
print(json.dumps(bind(P/'capture-pins-v1.json')))
